#!/usr/bin/env python3

"""
External Transfer Switch with Generator Auto Current Derating

This script combines two functions:
1. External transfer switch integration for MultiPlus/Quattro inverters
2. Generator auto current derating based on temperature and altitude

When a transfer between generator and shore power is initiated, an atomic lock
prevents other processes from interfering until the transfer is complete and verified.
"""

import platform
import argparse
import logging
import sys
import subprocess
import os
import time
import dbus
import configparser
import threading
from enum import Enum
from functools import partial

from gi.repository import GLib
from dbus.mainloop.glib import DBusGMainLoop

sys.path.insert(
    1,
    "/opt/victronenergy/dbus-systemcalc-py/ext/velib_python"
)

from vedbus import VeDbusService, VeDbusItemImport
from ve_utils import wrap_dbus_value
from settingsdevice import SettingsDevice

# D-Bus service names and paths
VEBUS_SERVICE_BASE = "com.victronenergy.vebus"
GENERATOR_SERVICE_BASE = "com.victronenergy.generator"
TEMPERATURE_SERVICE_BASE = "com.victronenergy.temperature"
SETTINGS_SERVICE_NAME = "com.victronenergy.settings"
GPS_SERVICE_BASE = "com.victronenergy.gps"
DIGITAL_INPUT_SERVICE_BASE = "com.victronenergy.digitalinput"
SYSTEM_SERVICE = "com.victronenergy.system"

ALTITUDE_PATH = "/Altitude"
AC_ACTIVE_INPUT_CURRENT_LIMIT_PATH = "/Ac/ActiveIn/CurrentLimit"
AC_INPUT_1_PATH = "/Settings/SystemSetup/AcInput1"
AC_INPUT_2_PATH = "/Settings/SystemSetup/AcInput2"
NUMBER_OF_AC_INPUTS_PATH = "/Ac/NumberOfAcInputs"
CURRENT_LIMIT_PATH = "/Ac/ActiveIn/CurrentLimit"
CURRENT_LIMIT_IS_ADJUSTABLE_PATH = "/Ac/ActiveIn/CurrentLimitIsAdjustable"
IGNORE_AC_IN_1_PATH = "/Ac/Control/IgnoreAcIn1"
REMOTE_GENERATOR_SELECTED_PATH = "/Ac/Control/RemoteGeneratorSelected"
TEMPERATURE_PATH = "/Temperature"
CUSTOM_NAME_PATH = "/CustomName"
STATE_PATH = "/State"
PRODUCT_NAME_PATH = "/ProductName"
BUS_ITEM_INTERFACE = "com.victronenergy.BusItem"
GENERATOR_CURRENT_LIMIT_PATH = "/Settings/TransferSwitch/GeneratorCurrentLimit"
GRID_CURRENT_LIMIT_PATH = "/Settings/TransferSwitch/GridCurrentLimit"

# Transfer switch state values
GENERATOR_ON_VALUE = (12, 3)
SHORE_POWER_ON_VALUE = (13, 2)

# Gen Auto Current State Values
GEN_AUTO_CURRENT_OFF = 2
GEN_AUTO_CURRENT_ON = 3

# Configuration file path
script_dir = os.path.dirname(os.path.abspath(__file__))
CONFIG_FILE_PATH = os.path.join(script_dir, 'config.ini')

class TransferState(Enum):
    """Transfer state machine states"""
    IDLE = "idle"
    TRANSFERRING_TO_GENERATOR = "transferring_to_generator"
    TRANSFERRING_TO_GRID = "transferring_to_grid"
    WAITING_FOR_GENERATOR_SHUTDOWN = "waiting_for_generator_shutdown"

class AtomicTransferLock:
    """Atomic lock to prevent concurrent transfers"""
    def __init__(self):
        self._lock = threading.Lock()
        self._is_locked = False
        self._holder = None
        
    def acquire(self, holder="unknown", timeout=0):
        """Acquire the lock with optional timeout in seconds (0 = non-blocking)"""
        start_time = time.time()
        while True:
            with self._lock:
                if not self._is_locked:
                    self._is_locked = True
                    self._holder = holder
                    logging.info(f"🔒 Lock acquired by: {holder}")
                    return True
            
            if timeout <= 0:
                return False
            
            if time.time() - start_time >= timeout:
                logging.warning(f"Lock acquire timeout for {holder} after {timeout}s")
                return False
            
            time.sleep(0.1)
    
    def release(self, holder="unknown"):
        with self._lock:
            if self._is_locked and self._holder == holder:
                self._is_locked = False
                self._holder = None
                logging.info(f"🔓 Lock released by: {holder}")
                return True
            logging.debug(f"Cannot release lock - held by {self._holder}, requested by {holder}")
            return False
    
    def is_held_by(self, holder):
        with self._lock:
            return self._is_locked and self._holder == holder
            
    @property
    def is_locked(self):
        with self._lock:
            return self._is_locked

class DynamicTransferSwitch:
    def __init__(self):
        # Setup DBus main loop
        DBusGMainLoop(set_as_default=True)
        self.bus = dbus.SystemBus()
        
        # Load configuration
        self._load_and_set_config()
        
        # Transfer switch state
        self.onGenerator = False
        self.lastOnGenerator = None
        self.transfer_state = TransferState.IDLE
        self.transfer_lock = AtomicTransferLock()
        
        # Startup synchronization
        self.startup_sync_complete = False
        self.startup_sequence_run = False
        self._initial_derating_done = False
        
        # VE.Bus direct objects
        self.vebus_service = None
        self.number_of_ac_inputs = None
        self.ac_input_type_obj = None
        self.current_limit_obj = None
        self.current_limit_is_adjustable_obj = None
        self.ignore_ac_in_1_obj = None
        self.remote_generator_selected_item = None
        self.remote_generator_selected_local_value = -1
        
        # Signal match tracking for critical properties
        self.active_matches = {}
        
        # Track discovered service names
        self.outdoor_temp_service = None
        self.generator_temp_service = None
        self.gps_service = None
        self.transfer_switch_service = None
        self.gen_auto_current_service = None
        
        # Track if services have ever been found
        self.vebus_found = False
        self.transfer_switch_found = False
        self.outdoor_temp_found = False
        self.generator_temp_found = False
        self.gps_found = False
        self.gen_auto_current_found = False
        
        # Sensor values
        self.outdoor_temp_fahrenheit = self.DEFAULT_OUTDOOR_TEMP_F
        self.altitude_feet = self.DEFAULT_ALTITUDE_FEET
        self.generator_temp_fahrenheit = self.DEFAULT_GENERATOR_TEMP_F
        self.gen_auto_current_state = None
        self.previous_gen_auto_current_state = None
        
        # Service discovery state
        self.transferSwitchActive = False
        self.transferSwitchLocation = 0
        self.initial_derated_output_logged = False
        
        # Track last derated value to avoid unnecessary writes
        self.last_derated_active_limit = None
        self.last_derated_gen_setting = None
        
        # Setup D-Bus settings
        self._setup_settings()
        
        # Setup name owner changed monitoring for critical services
        self.bus.add_signal_receiver(
            self._on_name_owner_changed,
            bus_name="org.freedesktop.DBus",
            dbus_interface="org.freedesktop.DBus",
            signal_name="NameOwnerChanged"
        )
        
        # Setup ItemsChanged monitoring for sensors and digital inputs (auto-recoverable)
        self.items_changed_services = {}
        
        # Start service discovery
        self._discovery_attempts = 0
        GLib.idle_add(self._discover_services)
        
        # Add periodic status reporting (every 60 seconds) - DEBUG level
        GLib.timeout_add_seconds(60, self._periodic_status)
    
    def _register_items_changed_service(self, service_name, callback):
        """Register a service for ItemsChanged monitoring"""
        if service_name in self.items_changed_services:
            return
        
        try:
            match = self.bus.add_signal_receiver(
                lambda items, **kwargs: self._on_items_changed(items, kwargs, callback),
                bus_name=service_name,
                path="/",
                dbus_interface="com.victronenergy.BusItem",
                signal_name="ItemsChanged",
                sender_keyword='sender_name'
            )
            self.items_changed_services[service_name] = match
            logging.info(f"✅ ItemsChanged monitoring for {service_name}")
            return True
        except Exception as e:
            logging.error(f"Failed to setup ItemsChanged for {service_name}: {e}")
            return False
    
    def _on_items_changed(self, items, kwargs, callback):
        """Handle ItemsChanged signals"""
        if not self.startup_sync_complete:
            return
        
        if not isinstance(items, dict):
            return
        
        for path, changes in items.items():
            if 'Value' in changes:
                try:
                    callback(path, changes['Value'])
                except Exception as e:
                    logging.error(f"Error in ItemsChanged callback: {e}")
    
    def _setup_settings(self):
        """Setup D-Bus settings device"""
        settingsList = {
            'gridCurrentLimit': ['/Settings/TransferSwitch/GridCurrentLimit', 0.0, 0.0, 0.0],
            'generatorCurrentLimit': ['/Settings/TransferSwitch/GeneratorCurrentLimit', 0.0, 0.0, 0.0],
            'gridInputType': ['/Settings/TransferSwitch/GridType', 0, 0, 0],
            'stopWhenAcAvailable': ['/Settings/TransferSwitch/StopWhenAcAvailable', 0, 0, 0],
            'stopWhenAcAvailableFp': ['/Settings/TransferSwitch/StopWhenAcAvailableFp', 0, 0, 0],
            'transferSwitchOnAc2': ['/Settings/TransferSwitch/TransferSwitchOnAc2', 0, 0, 0],
        }

        self.DbusSettings = SettingsDevice(
            bus=self.bus,
            supportedSettings=settingsList,
            timeout=10,
            eventCallback=self._on_settings_device_changed
        )
        
        if not self._validate_settings():
            logging.error("Initial settings validation failed")

        if self.DbusSettings['gridInputType'] == 2:
            logging.warning("grid input type was generator - resetting to grid")
            self.DbusSettings['gridInputType'] = 1
        
        # Subscribe to saved limits via PropertiesChanged
        self._subscribe_to_saved_limits()
    
    def _on_settings_device_changed(self, setting, old_value, new_value):
        """SettingsDevice callback - just for logging, sync handled by PropertiesChanged"""
        logging.debug(f"SettingsDevice: {setting} = {new_value} (was {old_value})")
    
    def _load_and_set_config(self):
        config = configparser.ConfigParser()
        
        # Defaults
        self.BASE_TEMPERATURE_THRESHOLD_F = 77.0
        self.TEMP_COEFFICIENT = 0.006
        self.ALTITUDE_COEFFICIENT = 0.000045
        self.BASE_GENERATOR_OUTPUT_AMPS = 56.0
        self.OUTPUT_BUFFER = 0.9
        self.HIGH_GENTEMP_THRESHOLD_F = 220.0
        self.MEDIUM_GENTEMP_THRESHOLD_F = 212.0
        self.HIGH_GENTEMP_REDUCTION = 0.85
        self.MEDIUM_GENTEMP_REDUCTION = 0.90
        self.DEFAULT_ALTITUDE_FEET = 1000.0
        self.DEFAULT_GENERATOR_TEMP_F = 180.0
        self.DEFAULT_OUTDOOR_TEMP_F = 77.0
        self.SHUTDOWN_TIMER_SECONDS = 10
        self.extTransferDigInputName = "transfer switch"
        
        if not os.path.exists(CONFIG_FILE_PATH):
            logging.warning(f"Config file not found at {CONFIG_FILE_PATH}")
            return
            
        try:
            config.read(CONFIG_FILE_PATH)
            logging.info(f"Loaded config from {CONFIG_FILE_PATH}")
            
            self.BASE_TEMPERATURE_THRESHOLD_F = config.getfloat('DeratingConstants', 'BaseTemperatureThresholdF', fallback=self.BASE_TEMPERATURE_THRESHOLD_F)
            self.TEMP_COEFFICIENT = config.getfloat('DeratingConstants', 'TempCoefficient', fallback=self.TEMP_COEFFICIENT)
            self.ALTITUDE_COEFFICIENT = config.getfloat('DeratingConstants', 'AltitudeCoefficient', fallback=self.ALTITUDE_COEFFICIENT)
            self.BASE_GENERATOR_OUTPUT_AMPS = config.getfloat('DeratingConstants', 'BaseGeneratorOutputAmps', fallback=self.BASE_GENERATOR_OUTPUT_AMPS)
            self.OUTPUT_BUFFER = config.getfloat('DeratingConstants', 'OutputBuffer', fallback=self.OUTPUT_BUFFER)
            self.HIGH_GENTEMP_THRESHOLD_F = config.getfloat('DeratingConstants', 'HighGenTempThresholdF', fallback=self.HIGH_GENTEMP_THRESHOLD_F)
            self.MEDIUM_GENTEMP_THRESHOLD_F = config.getfloat('DeratingConstants', 'MediumGenTempThresholdF', fallback=self.MEDIUM_GENTEMP_THRESHOLD_F)
            self.HIGH_GENTEMP_REDUCTION = config.getfloat('DeratingConstants', 'HighGenTempReduction', fallback=self.HIGH_GENTEMP_REDUCTION)
            self.MEDIUM_GENTEMP_REDUCTION = config.getfloat('DeratingConstants', 'MediumGenTempReduction', fallback=self.MEDIUM_GENTEMP_REDUCTION)
            self.DEFAULT_ALTITUDE_FEET = config.getfloat('DefaultSensorValues', 'DefaultAltitudeFeet', fallback=self.DEFAULT_ALTITUDE_FEET)
            self.DEFAULT_GENERATOR_TEMP_F = config.getfloat('DefaultSensorValues', 'DefaultGeneratorTempF', fallback=self.DEFAULT_GENERATOR_TEMP_F)
            self.DEFAULT_OUTDOOR_TEMP_F = config.getfloat('DefaultSensorValues', 'DefaultOutdoorTempF', fallback=self.DEFAULT_OUTDOOR_TEMP_F)
            
            if config.has_section('TransferSwitchSettings'):
                self.SHUTDOWN_TIMER_SECONDS = config.getfloat('TransferSwitchSettings', 'shutdown_timer', fallback=self.SHUTDOWN_TIMER_SECONDS)
            
            logging.info(f"Generator shutdown timer: {self.SHUTDOWN_TIMER_SECONDS}s")
            logging.info(f"Derating constants: BaseTemp={self.BASE_TEMPERATURE_THRESHOLD_F}F, TempCoeff={self.TEMP_COEFFICIENT}, AltCoeff={self.ALTITUDE_COEFFICIENT}")
            logging.info(f"Generator: BaseAmps={self.BASE_GENERATOR_OUTPUT_AMPS}A, Buffer={self.OUTPUT_BUFFER}")
            
        except (configparser.Error, ValueError) as e:
            logging.error(f"Error reading config: {e}")
    
    # Critical Property Monitoring (PropertiesChanged with recovery)
    def _subscribe_to_saved_limits(self):
        """Subscribe to saved current limit changes using PropertiesChanged"""
        # Generator current limit
        gen_key = f"{SETTINGS_SERVICE_NAME}{GENERATOR_CURRENT_LIMIT_PATH}"
        if gen_key not in self.active_matches:
            try:
                match = self.bus.add_signal_receiver(
                    lambda *args, **kwargs: self._on_generator_limit_changed(*args, **kwargs),
                    bus_name=SETTINGS_SERVICE_NAME,
                    path=GENERATOR_CURRENT_LIMIT_PATH,
                    dbus_interface="com.victronenergy.BusItem",
                    signal_name="PropertiesChanged",
                    path_keyword='path',
                    sender_keyword='sender_name'
                )
                self.active_matches[gen_key] = match
                logging.info(f"✅ Subscribed to generator current limit")
            except Exception as e:
                logging.error(f"Failed to subscribe to generator limit: {e}")
        
        # Grid current limit
        grid_key = f"{SETTINGS_SERVICE_NAME}{GRID_CURRENT_LIMIT_PATH}"
        if grid_key not in self.active_matches:
            try:
                match = self.bus.add_signal_receiver(
                    lambda *args, **kwargs: self._on_grid_limit_changed(*args, **kwargs),
                    bus_name=SETTINGS_SERVICE_NAME,
                    path=GRID_CURRENT_LIMIT_PATH,
                    dbus_interface="com.victronenergy.BusItem",
                    signal_name="PropertiesChanged",
                    path_keyword='path',
                    sender_keyword='sender_name'
                )
                self.active_matches[grid_key] = match
                logging.info(f"✅ Subscribed to grid current limit")
            except Exception as e:
                logging.error(f"Failed to subscribe to grid limit: {e}")
    
    def _subscribe_to_active_limit(self, service_name):
        """Subscribe to active current limit changes using PropertiesChanged"""
        key = f"{service_name}{AC_ACTIVE_INPUT_CURRENT_LIMIT_PATH}"
        
        if key in self.active_matches:
            return
        
        try:
            match = self.bus.add_signal_receiver(
                lambda *args, **kwargs: self._on_active_limit_changed(*args, **kwargs),
                bus_name=service_name,
                path=AC_ACTIVE_INPUT_CURRENT_LIMIT_PATH,
                dbus_interface="com.victronenergy.BusItem",
                signal_name="PropertiesChanged",
                path_keyword='path',
                sender_keyword='sender_name'
            )
            self.active_matches[key] = match
            self.vebus_service = service_name
            logging.info(f"✅ Subscribed to active current limit on {service_name}")
            
            # Read initial value
            self._read_initial_active_limit()
            return True
        except Exception as e:
            logging.error(f"Failed to subscribe to active limit: {e}")
            return False
    
    def _unsubscribe_from_active_limit(self, service_name):
        """Unsubscribe from active current limit changes"""
        key = f"{service_name}{AC_ACTIVE_INPUT_CURRENT_LIMIT_PATH}"
        
        if key in self.active_matches:
            try:
                self.active_matches[key].remove()
                del self.active_matches[key]
                logging.info(f"🔴 Unsubscribed from active current limit on {service_name}")
            except Exception as e:
                logging.error(f"Failed to unsubscribe: {e}")
    
    def _read_initial_active_limit(self):
        """Read initial active current limit value"""
        if self.vebus_service:
            try:
                # Use the standard BusItem interface
                obj = self.bus.get_object(self.vebus_service, AC_ACTIVE_INPUT_CURRENT_LIMIT_PATH)
                iface = dbus.Interface(obj, BUS_ITEM_INTERFACE)
                value = iface.GetValue()
                logging.info(f"📖 Initial active current limit: {value}A")
                self._handle_active_limit_change(float(value))
            except Exception as e:
                logging.error(f"Failed to read initial active limit: {e}")
    
    def _on_name_owner_changed(self, name, old_owner, new_owner):
        """Handle service appearance/disappearance for critical properties"""
        # Handle VE.Bus service (active current limit)
        if name.startswith(VEBUS_SERVICE_BASE):
            if new_owner and not old_owner:
                logging.info(f"🟢 VE.Bus connected: {name}")
                self._subscribe_to_active_limit(name)
                # Also re-setup VE.Bus objects
                if not self.vebus_service:
                    self.vebus_service = name
                    self._setup_vebus_objects()
            elif old_owner and not new_owner:
                logging.warning(f"🔴 VE.Bus disconnected: {name}")
                self._unsubscribe_from_active_limit(name)
                self.vebus_service = None
        
        # Handle Settings service (saved current limits)
        elif name == SETTINGS_SERVICE_NAME:
            if new_owner and not old_owner:
                logging.info(f"🟢 Settings service connected: {name}")
                self._subscribe_to_saved_limits()
            elif old_owner and not new_owner:
                logging.warning(f"🔴 Settings service disconnected: {name}")
                for key in list(self.active_matches.keys()):
                    if SETTINGS_SERVICE_NAME in key:
                        try:
                            self.active_matches[key].remove()
                            del self.active_matches[key]
                        except:
                            pass
                logging.info("🔴 Unsubscribed from saved current limits")
    
    # PropertiesChanged Callbacks
    def _on_active_limit_changed(self, *args, **kwargs):
        """Callback for active current limit changes"""
        if not self.startup_sync_complete:
            return
        
        if args and isinstance(args[0], dict):
            payload = args[0]
            if 'Value' in payload:
                new_limit = payload['Value']
                logging.info(f"🔌 ACTIVE LIMIT CHANGE: {new_limit}A")
                self._handle_active_limit_change(float(new_limit))
    
    def _on_generator_limit_changed(self, *args, **kwargs):
        """Callback for generator current limit changes"""
        if not self.startup_sync_complete:
            return
        
        if args and isinstance(args[0], dict):
            payload = args[0]
            if 'Value' in payload:
                new_limit = payload['Value']
                logging.info(f"⚙️ GENERATOR LIMIT CHANGE: {new_limit}A")
                self._handle_generator_limit_change(float(new_limit))
    
    def _on_grid_limit_changed(self, *args, **kwargs):
        """Callback for grid current limit changes"""
        if not self.startup_sync_complete:
            return
        
        if args and isinstance(args[0], dict):
            payload = args[0]
            if 'Value' in payload:
                new_limit = payload['Value']
                logging.info(f"⚙️ GRID LIMIT CHANGE: {new_limit}A")
                self._handle_grid_limit_change(float(new_limit))
    
    # Limit Change Handlers
    def _handle_active_limit_change(self, new_limit):
        """Handle active limit change - sync to saved settings"""
        if self.transfer_state != TransferState.IDLE:
            logging.debug(f"Active limit change ignored - transfer in progress")
            return
        
        # Get current input type
        try:
            current_input_type = self.ac_input_type_obj.GetValue() if self.ac_input_type_obj else None
        except Exception as e:
            logging.error(f"Failed to get input type: {e}")
            return
        
        # If Gen Auto is ON and generator is running, override
        if self.gen_auto_current_state == GEN_AUTO_CURRENT_ON and self._is_generator_running():
            logging.info("Gen Auto ON - overriding external change with derated value")
            GLib.idle_add(lambda: self._perform_derating(AC_ACTIVE_INPUT_CURRENT_LIMIT_PATH, force=True))
            GLib.idle_add(lambda: self._perform_derating(GENERATOR_CURRENT_LIMIT_PATH, force=True))
            return
        
        # Sync active limit to saved setting
        if current_input_type == 2:  # On generator
            if self.gen_auto_current_state != GEN_AUTO_CURRENT_ON:
                current_saved = self.DbusSettings['generatorCurrentLimit']
                if abs(new_limit - current_saved) > 0.1:
                    logging.info(f"🔄 SYNC: Updating saved generator limit from {current_saved}A to {new_limit}A")
                    self.DbusSettings['generatorCurrentLimit'] = new_limit
                    self.last_derated_gen_setting = new_limit
        elif current_input_type in (1, 3):  # On grid or shore
            current_saved = self.DbusSettings['gridCurrentLimit']
            if abs(new_limit - current_saved) > 0.1:
                logging.info(f"🔄 SYNC: Updating saved grid limit from {current_saved}A to {new_limit}A")
                self.DbusSettings['gridCurrentLimit'] = new_limit
    
    def _handle_generator_limit_change(self, new_limit):
        """Handle saved generator limit change - sync to active if on generator"""
        if self.transfer_state != TransferState.IDLE:
            return
        
        # Update the settings device
        self.DbusSettings['generatorCurrentLimit'] = new_limit
        self.last_derated_gen_setting = new_limit
        
        # If Gen Auto is ON, override
        if self.gen_auto_current_state == GEN_AUTO_CURRENT_ON:
            logging.info("Gen Auto ON - overriding with derated value")
            GLib.idle_add(lambda: self._perform_derating(GENERATOR_CURRENT_LIMIT_PATH, force=True))
            if self._is_generator_running():
                GLib.idle_add(lambda: self._perform_derating(AC_ACTIVE_INPUT_CURRENT_LIMIT_PATH, force=True))
            return
        
        # Apply to active limit if on generator
        try:
            current_input_type = self.ac_input_type_obj.GetValue() if self.ac_input_type_obj else None
            if current_input_type == 2:
                if self.current_limit_is_adjustable_obj and self.current_limit_is_adjustable_obj.GetValue() == 1:
                    logging.info(f"🔄 SYNC: Applying generator limit {new_limit}A to active")
                    self.current_limit_obj.SetValue(wrap_dbus_value(new_limit))
                    self.last_derated_active_limit = new_limit
        except Exception as e:
            logging.error(f"Failed to apply generator limit to active: {e}")
    
    def _handle_grid_limit_change(self, new_limit):
        """Handle saved grid limit change - sync to active if on grid/shore"""
        if self.transfer_state != TransferState.IDLE:
            return
        
        # Update the settings device
        self.DbusSettings['gridCurrentLimit'] = new_limit
        
        # Apply to active limit if on grid or shore
        try:
            current_input_type = self.ac_input_type_obj.GetValue() if self.ac_input_type_obj else None
            if current_input_type in (1, 3):
                if self.current_limit_is_adjustable_obj and self.current_limit_is_adjustable_obj.GetValue() == 1:
                    logging.info(f"🔄 SYNC: Applying grid limit {new_limit}A to active")
                    self.current_limit_obj.SetValue(wrap_dbus_value(new_limit))
                    self.last_derated_active_limit = new_limit
        except Exception as e:
            logging.error(f"Failed to apply grid limit to active: {e}")
    
    # Service Discovery Methods
    def _discover_services(self):
        """Discover all required services"""
        self._discovery_attempts += 1
        logging.info(f"Service discovery attempt {self._discovery_attempts}")
        
        # Find VE.Bus service (required)
        if not self.vebus_found:
            if self._find_vebus_service():
                self.vebus_found = True
        
        # Find transfer switch (required)
        if not self.transfer_switch_found:
            if self._find_transfer_switch_input():
                self.transfer_switch_found = True
        
        # Find outdoor temperature sensor
        if not self.outdoor_temp_found:
            if self._find_outdoor_temperature_sensor():
                self.outdoor_temp_found = True
        
        # Find generator temperature sensor
        if not self.generator_temp_found:
            if self._find_generator_temperature_sensor():
                self.generator_temp_found = True
        
        # Find GPS
        if not self.gps_found:
            if self._find_gps_service():
                self.gps_found = True
        
        # Find Gen Auto Current
        if not self.gen_auto_current_found:
            if self._find_gen_auto_current_input():
                self.gen_auto_current_found = True
        
        # Check if we have required services
        if self.vebus_found and self.transfer_switch_found:
            if not self.startup_sync_complete:
                self._perform_startup_sync()
            
            # Only retry for services that have NEVER been found
            missing_optional = []
            if not self.outdoor_temp_found:
                missing_optional.append("outdoor_temp")
            if not self.generator_temp_found:
                missing_optional.append("generator_temp")
            if not self.gps_found:
                missing_optional.append("gps")
            if not self.gen_auto_current_found:
                missing_optional.append("gen_auto_current")
            
            if missing_optional:
                logging.info(f"Still looking for optional services: {', '.join(missing_optional)}")
                GLib.timeout_add_seconds(60, self._discover_services)
            else:
                logging.info("All services discovered - stopping discovery")
                return
        else:
            missing_required = []
            if not self.vebus_found:
                missing_required.append("VE.Bus")
            if not self.transfer_switch_found:
                missing_required.append("Transfer Switch")
            logging.warning(f"Required services missing: {', '.join(missing_required)} - retrying in 30s")
            GLib.timeout_add_seconds(30, self._discover_services)
    
    def _find_vebus_service(self):
        """Find VE.Bus service and subscribe to active limit"""
        services = [name for name in self.bus.list_names() if name.startswith(VEBUS_SERVICE_BASE)]
        if services:
            self.vebus_service = services[0]
            self._setup_vebus_objects()
            self._subscribe_to_active_limit(self.vebus_service)
            logging.info(f"✅ Found VE.Bus: {self.vebus_service}")
            return True
        return False
    
    def _setup_vebus_objects(self):
        """Set up VE.Bus D-Bus objects"""
        try:
            obj = self.bus.get_object(self.vebus_service, NUMBER_OF_AC_INPUTS_PATH)
            self.number_of_ac_inputs = obj.GetValue()
            logging.info(f"Number of AC inputs: {self.number_of_ac_inputs}")
            
            self.current_limit_obj = self.bus.get_object(self.vebus_service, CURRENT_LIMIT_PATH)
            self.current_limit_is_adjustable_obj = self.bus.get_object(self.vebus_service, CURRENT_LIMIT_IS_ADJUSTABLE_PATH)
            self.ignore_ac_in_1_obj = self.bus.get_object(self.vebus_service, IGNORE_AC_IN_1_PATH)
            
            is_adjustable = self.current_limit_is_adjustable_obj.GetValue()
            logging.info(f"Current limit adjustable: {is_adjustable}")
            
            try:
                self.remote_generator_selected_item = self.bus.get_object(self.vebus_service, REMOTE_GENERATOR_SELECTED_PATH)
            except:
                self.remote_generator_selected_item = None
            
            # Setup AC input type
            if self.number_of_ac_inputs == 2:
                ac_input_path = AC_INPUT_2_PATH
            else:
                ac_input_path = AC_INPUT_1_PATH
            
            self.ac_input_type_obj = self.bus.get_object(SETTINGS_SERVICE_NAME, ac_input_path)
            logging.info(f"AC input type path: {ac_input_path}")
            logging.info(f"Initial AC input type: {self.ac_input_type_obj.GetValue()}")
            
            logging.info(f"Discovered {'Quattro' if self.number_of_ac_inputs == 2 else 'MultiPlus'}")
        except Exception as e:
            logging.error(f"Failed to setup VE.Bus: {e}")
    
    def _find_transfer_switch_input(self):
        """Find digital input configured as transfer switch"""
        for service in self.bus.list_names():
            if service.startswith(DIGITAL_INPUT_SERVICE_BASE):
                try:
                    obj = self.bus.get_object(service, PRODUCT_NAME_PATH)
                    name = dbus.Interface(obj, BUS_ITEM_INTERFACE).GetValue()
                    if name and "transfer switch" in name.lower():
                        self.transfer_switch_service = service
                        self.transferSwitchActive = True
                        
                        self._register_items_changed_service(
                            service,
                            self._on_transfer_switch_value
                        )
                        
                        logging.info(f"✅ Found transfer switch: {service}")
                        return True
                except:
                    pass
        return False
    
    def _find_gen_auto_current_input(self):
        """Find digital input for Gen Auto Current"""
        for service in self.bus.list_names():
            if service.startswith(DIGITAL_INPUT_SERVICE_BASE):
                try:
                    obj = self.bus.get_object(service, PRODUCT_NAME_PATH)
                    name = dbus.Interface(obj, BUS_ITEM_INTERFACE).GetValue()
                    if name and "gen auto current" in name.lower():
                        self.gen_auto_current_service = service
                        
                        self._register_items_changed_service(
                            service,
                            self._on_gen_auto_current_value
                        )
                        
                        # Get initial state
                        try:
                            state_obj = self.bus.get_object(service, STATE_PATH)
                            state_iface = dbus.Interface(state_obj, BUS_ITEM_INTERFACE)
                            state = state_iface.GetValue()
                            if state is not None:
                                self.gen_auto_current_state = int(state)
                                logging.info(f"✅ Found Gen Auto Current: {service} - Initial state: {'ON' if self.gen_auto_current_state == GEN_AUTO_CURRENT_ON else 'OFF'}")
                                
                                if self.gen_auto_current_state == GEN_AUTO_CURRENT_ON:
                                    logging.info("Gen Auto Current enabled - forcing derating")
                                    GLib.idle_add(self._force_derating)
                        except Exception as e:
                            logging.error(f"Failed to read initial Gen Auto state: {e}")
                        
                        return True
                except:
                    pass
        return False
    
    def _find_outdoor_temperature_sensor(self):
        """Find temperature sensor with 'outdoor' in custom name"""
        for service in self.bus.list_names():
            if service.startswith(TEMPERATURE_SERVICE_BASE):
                try:
                    obj = self.bus.get_object(service, CUSTOM_NAME_PATH)
                    name = dbus.Interface(obj, BUS_ITEM_INTERFACE).GetValue()
                    if name and "outdoor" in name.lower():
                        self.outdoor_temp_service = service
                        
                        self._register_items_changed_service(
                            service,
                            self._on_outdoor_temp_value
                        )
                        
                        logging.info(f"✅ Found outdoor temp sensor: {service}")
                        
                        # Get initial value
                        try:
                            temp_obj = self.bus.get_object(service, TEMPERATURE_PATH)
                            temp_iface = dbus.Interface(temp_obj, BUS_ITEM_INTERFACE)
                            temp_c = temp_iface.GetValue()
                            if temp_c is not None:
                                self.outdoor_temp_fahrenheit = (temp_c * 9/5) + 32
                                logging.info(f"   Initial value: {self.outdoor_temp_fahrenheit:.1f}F")
                                GLib.idle_add(self._trigger_derating)
                        except Exception as e:
                            logging.error(f"Failed to read initial temp: {e}")
                        
                        return True
                except:
                    continue
        return False
    
    def _find_generator_temperature_sensor(self):
        """Find temperature sensor for generator"""
        search_patterns = ["gen", "generator", "gen temp", "generator temp"]
        
        for service in self.bus.list_names():
            if service.startswith(TEMPERATURE_SERVICE_BASE):
                try:
                    obj = self.bus.get_object(service, CUSTOM_NAME_PATH)
                    name = dbus.Interface(obj, BUS_ITEM_INTERFACE).GetValue()
                    if name:
                        name_lower = name.lower()
                        for pattern in search_patterns:
                            if pattern in name_lower:
                                self.generator_temp_service = service
                                
                                self._register_items_changed_service(
                                    service,
                                    self._on_generator_temp_value
                                )
                                
                                logging.info(f"✅ Found generator temp sensor: {service}")
                                
                                # Get initial value
                                try:
                                    temp_obj = self.bus.get_object(service, TEMPERATURE_PATH)
                                    temp_iface = dbus.Interface(temp_obj, BUS_ITEM_INTERFACE)
                                    temp_c = temp_iface.GetValue()
                                    if temp_c is not None:
                                        self.generator_temp_fahrenheit = (temp_c * 9/5) + 32
                                        logging.info(f"   Initial value: {self.generator_temp_fahrenheit:.1f}F")
                                        GLib.idle_add(self._trigger_derating)
                                except Exception as e:
                                    logging.error(f"Failed to read initial temp: {e}")
                                
                                return True
                except:
                    pass
                
                try:
                    obj = self.bus.get_object(service, PRODUCT_NAME_PATH)
                    name = dbus.Interface(obj, BUS_ITEM_INTERFACE).GetValue()
                    if name:
                        name_lower = name.lower()
                        for pattern in search_patterns:
                            if pattern in name_lower:
                                self.generator_temp_service = service
                                
                                self._register_items_changed_service(
                                    service,
                                    self._on_generator_temp_value
                                )
                                
                                logging.info(f"✅ Found generator temp sensor: {service}")
                                
                                # Get initial value
                                try:
                                    temp_obj = self.bus.get_object(service, TEMPERATURE_PATH)
                                    temp_iface = dbus.Interface(temp_obj, BUS_ITEM_INTERFACE)
                                    temp_c = temp_iface.GetValue()
                                    if temp_c is not None:
                                        self.generator_temp_fahrenheit = (temp_c * 9/5) + 32
                                        logging.info(f"   Initial value: {self.generator_temp_fahrenheit:.1f}F")
                                        GLib.idle_add(self._trigger_derating)
                                except Exception as e:
                                    logging.error(f"Failed to read initial temp: {e}")
                                
                                return True
                except:
                    pass
        return False
    
    def _find_gps_service(self):
        """Find GPS service for altitude"""
        services = [name for name in self.bus.list_names() if name.startswith(GPS_SERVICE_BASE)]
        if services:
            self.gps_service = services[0]
            
            self._register_items_changed_service(
                self.gps_service,
                self._on_altitude_value
            )
            
            logging.info(f"✅ Found GPS: {self.gps_service}")
            
            # Get initial value
            try:
                alt_obj = self.bus.get_object(self.gps_service, ALTITUDE_PATH)
                alt_iface = dbus.Interface(alt_obj, BUS_ITEM_INTERFACE)
                alt = alt_iface.GetValue()
                if alt is not None:
                    try:
                        if isinstance(alt, dbus.Array):
                            alt_m = float(alt[0]) if alt else None
                        else:
                            alt_m = float(alt)
                        if alt_m is not None:
                            self.altitude_feet = alt_m * 3.28084
                            logging.info(f"   Initial altitude: {self.altitude_feet:.0f}ft")
                            GLib.idle_add(self._trigger_derating)
                    except:
                        pass
            except:
                pass
            
            return True
        return False
    
    # ItemsChanged Callbacks (Sensors and Digital Inputs)
    def _on_transfer_switch_value(self, path, value):
        """Handle transfer switch value changes"""
        if path != STATE_PATH:
            return
        
        new_state = value
        logging.info(f"Transfer switch state changed: {new_state}")
        
        if new_state in (12, 3):
            new_onGenerator = True
        elif new_state in (13, 2):
            new_onGenerator = False
        else:
            return
        
        if new_onGenerator != self.onGenerator:
            self.onGenerator = new_onGenerator
            logging.info(f"Transfer switch confirmed: {'GENERATOR' if self.onGenerator else 'GRID'}")
            
            self.update_remote_generator_selected()
            
            if self.onGenerator:
                if self.transfer_lock.acquire("transfer_switch", timeout=2):
                    try:
                        self._transfer_to_generator()
                    finally:
                        self.transfer_lock.release("transfer_switch")
            else:
                if self.transfer_lock.acquire("transfer_switch", timeout=2):
                    try:
                        self._transfer_to_grid()
                    except Exception as e:
                        logging.error(f"Error during grid transfer: {e}")
                        self.transfer_lock.release("transfer_switch")
    
    def _on_gen_auto_current_value(self, path, value):
        """Handle Gen Auto Current value changes"""
        if path != STATE_PATH:
            return
        
        new_state = int(value)
        old_state = self.gen_auto_current_state
        self.gen_auto_current_state = new_state
        
        logging.info(f"Gen Auto Current: {'ON' if new_state == GEN_AUTO_CURRENT_ON else 'OFF'}")
        
        if new_state == GEN_AUTO_CURRENT_ON:
            logging.info("Gen Auto Current enabled - forcing derating")
            GLib.idle_add(self._force_derating)
        else:
            logging.info("Gen Auto Current disabled - reverting to saved limit")
            GLib.idle_add(self._revert_to_saved_limit)
    
    def _on_outdoor_temp_value(self, path, value):
        """Handle outdoor temperature value changes"""
        if path != TEMPERATURE_PATH:
            return
        
        temp_c = value
        temp_f = (temp_c * 9/5) + 32
        old_temp = self.outdoor_temp_fahrenheit
        self.outdoor_temp_fahrenheit = temp_f
        logging.info(f"🌡️ Outdoor temp: {old_temp:.1f}F -> {temp_f:.1f}F")
        GLib.idle_add(self._trigger_derating)
    
    def _on_generator_temp_value(self, path, value):
        """Handle generator temperature value changes"""
        if path != TEMPERATURE_PATH:
            return
        
        temp_c = value
        temp_f = (temp_c * 9/5) + 32
        old_temp = self.generator_temp_fahrenheit
        self.generator_temp_fahrenheit = temp_f
        logging.info(f"🔧 Generator temp: {old_temp:.1f}F -> {temp_f:.1f}F")
        GLib.idle_add(self._trigger_derating)
    
    def _on_altitude_value(self, path, value):
        """Handle altitude value changes"""
        if path != ALTITUDE_PATH:
            return
        
        try:
            if isinstance(value, dbus.Array):
                alt_m = float(value[0]) if value else None
            else:
                alt_m = float(value)
            if alt_m is not None:
                old_alt = self.altitude_feet
                self.altitude_feet = alt_m * 3.28084
                if abs(old_alt - self.altitude_feet) > 10:
                    logging.info(f"🗻 Altitude: {old_alt:.0f}ft -> {self.altitude_feet:.0f}ft")
                GLib.idle_add(self._trigger_derating)
        except Exception as e:
            logging.debug(f"Error processing altitude: {e}")
    
    # Startup and Core Functions
    def _perform_startup_sync(self):
        """Perform initial synchronization after discovery"""
        logging.info("=" * 60)
        logging.info("STARTUP SYNCHRONIZATION")
        logging.info("=" * 60)
        
        lock_acquired = self.transfer_lock.acquire("startup", timeout=5)
        if not lock_acquired:
            logging.error("Could not acquire lock for startup")
            self.startup_sync_complete = True
            return
        
        try:
            time.sleep(2)
            
            # Get current values from D-Bus directly
            if self.transfer_switch_service:
                obj = self.bus.get_object(self.transfer_switch_service, STATE_PATH)
                iface = dbus.Interface(obj, BUS_ITEM_INTERFACE)
                state = iface.GetValue()
                if state in (12, 3):
                    self.onGenerator = True
                elif state in (13, 2):
                    self.onGenerator = False
                logging.info(f"Transfer Switch: {'GENERATOR' if self.onGenerator else 'GRID/SHORE'}")
            
            # Read current AC state
            try:
                current_input_type = self.ac_input_type_obj.GetValue()
                current_limit = self.current_limit_obj.GetValue() if self.current_limit_obj else None
                logging.info(f"Current AC Input: {current_input_type}")
                logging.info(f"Current Active Limit: {current_limit}A")
            except Exception as e:
                logging.error(f"Failed to read AC state: {e}")
                return
            
            saved_grid_limit = self.DbusSettings['gridCurrentLimit']
            saved_gen_limit = self.DbusSettings['generatorCurrentLimit']
            saved_grid_type = self.DbusSettings['gridInputType']
            
            logging.info(f"Saved Grid Limit: {saved_grid_limit}A")
            logging.info(f"Saved Generator Limit: {saved_gen_limit}A")
            
            # Apply correct settings
            if self.onGenerator:
                if current_input_type != 2:
                    logging.info("Applying generator settings...")
                    try:
                        self.ac_input_type_obj.SetValue(wrap_dbus_value(2))
                        if self.current_limit_is_adjustable_obj and self.current_limit_is_adjustable_obj.GetValue() == 1:
                            self.current_limit_obj.SetValue(wrap_dbus_value(saved_gen_limit))
                        time.sleep(1)
                        logging.info("Generator settings applied")
                    except Exception as e:
                        logging.error(f"Failed to apply generator settings: {e}")
            else:
                if current_input_type != saved_grid_type:
                    logging.info("Applying grid/shore settings...")
                    try:
                        self.ac_input_type_obj.SetValue(wrap_dbus_value(saved_grid_type))
                        if self.current_limit_is_adjustable_obj and self.current_limit_is_adjustable_obj.GetValue() == 1:
                            self.current_limit_obj.SetValue(wrap_dbus_value(saved_grid_limit))
                        time.sleep(1)
                        logging.info("Grid/Shore settings applied")
                    except Exception as e:
                        logging.error(f"Failed to apply grid settings: {e}")
            
            self.startup_sync_complete = True
            logging.info("=" * 60)
            logging.info("STARTUP COMPLETE - Normal operations")
            logging.info("=" * 60)
            
            GLib.idle_add(self._trigger_derating)
            
        except Exception as e:
            logging.error(f"Startup synchronization failed: {e}")
        finally:
            self.transfer_lock.release("startup")
    
    def _is_generator_running(self):
        """Check if generator is currently running"""
        if self.transfer_switch_service:
            try:
                obj = self.bus.get_object(self.transfer_switch_service, STATE_PATH)
                iface = dbus.Interface(obj, BUS_ITEM_INTERFACE)
                state = iface.GetValue()
                return state in GENERATOR_ON_VALUE
            except:
                pass
        return False
    
    def _trigger_derating(self):
        """Trigger derating calculation"""
        if not self.startup_sync_complete:
            return
        
        if self.transfer_state != TransferState.IDLE:
            return
        
        if self.gen_auto_current_state == GEN_AUTO_CURRENT_ON:
            if self._is_generator_running():
                self._perform_derating(AC_ACTIVE_INPUT_CURRENT_LIMIT_PATH, force=False)
                self._perform_derating(GENERATOR_CURRENT_LIMIT_PATH, force=False)
            else:
                self._perform_derating(GENERATOR_CURRENT_LIMIT_PATH, force=False)
    
    def _force_derating(self):
        """Force derating update"""
        if not self.startup_sync_complete:
            return
        
        if self.transfer_state != TransferState.IDLE:
            GLib.timeout_add_seconds(1, self._force_derating)
            return
        
        logging.info("Forcing derating update")
        
        if self._is_generator_running():
            self._perform_derating(AC_ACTIVE_INPUT_CURRENT_LIMIT_PATH, force=True)
            self._perform_derating(GENERATOR_CURRENT_LIMIT_PATH, force=True)
        else:
            self._perform_derating(GENERATOR_CURRENT_LIMIT_PATH, force=True)
    
    def _revert_to_saved_limit(self):
        """Revert to saved generator limit"""
        if self._is_generator_running():
            saved_limit = self.DbusSettings['generatorCurrentLimit']
            logging.info(f"Reverting to saved generator limit: {saved_limit}A")
            if self.vebus_service:
                self._set_dbus_value(self.vebus_service, AC_ACTIVE_INPUT_CURRENT_LIMIT_PATH, saved_limit)
                self.last_derated_active_limit = saved_limit
    
    def calculate_derating_factor(self, temp_f, alt_ft, gen_temp_f):
        """Calculate derated output"""
        temperature_multiplier = 1.0
        altitude_multiplier = 1.0
        generator_temp_multiplier = 1.0
        
        if temp_f is not None and temp_f > self.BASE_TEMPERATURE_THRESHOLD_F:
            temp_diff = temp_f - self.BASE_TEMPERATURE_THRESHOLD_F
            temp_reduction = temp_diff * self.TEMP_COEFFICIENT
            temperature_multiplier = 1.0 - temp_reduction
            temperature_multiplier = max(0.0, temperature_multiplier)
        
        if alt_ft is not None:
            alt_reduction = alt_ft * self.ALTITUDE_COEFFICIENT
            altitude_multiplier = 1.0 - alt_reduction
            altitude_multiplier = max(0.0, altitude_multiplier)
        
        if gen_temp_f is not None:
            if gen_temp_f >= self.HIGH_GENTEMP_THRESHOLD_F:
                generator_temp_multiplier = self.HIGH_GENTEMP_REDUCTION
            elif gen_temp_f >= self.MEDIUM_GENTEMP_THRESHOLD_F:
                generator_temp_multiplier = self.MEDIUM_GENTEMP_REDUCTION
        
        derated = self.BASE_GENERATOR_OUTPUT_AMPS
        derated = derated * temperature_multiplier
        derated = derated * altitude_multiplier
        derated = derated * generator_temp_multiplier
        derated = derated * self.OUTPUT_BUFFER
        
        return round(derated, 1)
    
    def _perform_derating(self, target_path, force=False):
        """Calculate and apply derated value"""
        if not self.startup_sync_complete:
            return
        
        if self.transfer_state != TransferState.IDLE:
            return
        
        try:
            derated = self.calculate_derating_factor(
                self.outdoor_temp_fahrenheit, self.altitude_feet, self.generator_temp_fahrenheit
            )
            
            if target_path == GENERATOR_CURRENT_LIMIT_PATH:
                service = SETTINGS_SERVICE_NAME
                desc = "Generator Limit"
                if not force and self.last_derated_gen_setting == derated:
                    return
            else:
                service = self.vebus_service
                desc = "Active Limit"
                if not force and self.last_derated_active_limit == derated:
                    return
            
            current, _ = self._get_dbus_value(service, target_path)
            
            if current is None or abs(float(current) - derated) > 0.05 or force:
                self._set_dbus_value(service, target_path, derated)
                logging.info(f"💡 {desc} updated to {derated}A")
                
                if target_path == GENERATOR_CURRENT_LIMIT_PATH:
                    self.last_derated_gen_setting = derated
                else:
                    self.last_derated_active_limit = derated
                    
        except Exception as e:
            logging.error(f"Derating failed: {e}")
    
    def _periodic_status(self):
        """Periodic status report - DEBUG level"""
        if self.startup_sync_complete:
            current_active = None
            try:
                if self.current_limit_obj:
                    current_active = self.current_limit_obj.GetValue()
            except:
                pass
            
            logging.debug(f"📊 STATUS - Gen Auto: {self.gen_auto_current_state} ({'ON' if self.gen_auto_current_state == GEN_AUTO_CURRENT_ON else 'OFF'}), "
                         f"Active Limit: {current_active}A, "
                         f"Saved Grid: {self.DbusSettings['gridCurrentLimit']}A, "
                         f"Saved Gen: {self.DbusSettings['generatorCurrentLimit']}A, "
                         f"Outdoor: {self.outdoor_temp_fahrenheit:.1f}F, "
                         f"Gen Temp: {self.generator_temp_fahrenheit:.1f}F, "
                         f"Gen Running: {self._is_generator_running()}")
        return True
    
    def _get_dbus_value(self, service_name, path):
        """Get D-Bus value"""
        if not service_name:
            return None, False
        try:
            obj = self.bus.get_object(service_name, path)
            interface = dbus.Interface(obj, BUS_ITEM_INTERFACE)
            return interface.GetValue(), False
        except:
            return None, False
    
    def _set_dbus_value(self, service_name, path, value):
        """Set D-Bus value"""
        if not service_name:
            return
        try:
            obj = self.bus.get_object(service_name, path)
            interface = dbus.Interface(obj, BUS_ITEM_INTERFACE)
            interface.SetValue(wrap_dbus_value(value))
        except Exception as e:
            logging.error(f"Failed to set {path}: {e}")
    
    def _transfer_to_generator(self):
        """Transfer to generator"""
        try:
            self.transfer_state = TransferState.TRANSFERRING_TO_GENERATOR
            logging.info("=== Transferring to GENERATOR ===")
            
            target_limit = self.DbusSettings['generatorCurrentLimit']
            
            self.ac_input_type_obj.SetValue(wrap_dbus_value(2))
            
            if self.current_limit_is_adjustable_obj and self.current_limit_is_adjustable_obj.GetValue() == 1:
                self.current_limit_obj.SetValue(wrap_dbus_value(target_limit))
                self.last_derated_active_limit = target_limit
            
            logging.info("=== Generator transfer complete ===")
            GLib.idle_add(self._trigger_derating)
            
        except Exception as e:
            logging.error(f"Generator transfer failed: {e}")
        finally:
            self.transfer_state = TransferState.IDLE
    
    def _transfer_to_grid(self):
        """Transfer to grid with delay"""
        try:
            self.transfer_state = TransferState.WAITING_FOR_GENERATOR_SHUTDOWN
            logging.info(f"Waiting {self.SHUTDOWN_TIMER_SECONDS}s for generator shutdown")
            GLib.timeout_add_seconds(int(self.SHUTDOWN_TIMER_SECONDS), self._execute_grid_transfer)
        except Exception as e:
            logging.error(f"Failed to initiate grid transfer: {e}")
            self.transfer_state = TransferState.IDLE
    
    def _execute_grid_transfer(self):
        """Execute grid transfer after delay"""
        try:
            self.transfer_state = TransferState.TRANSFERRING_TO_GRID
            logging.info("=== Transferring to GRID ===")
            
            try:
                ignore = self.ignore_ac_in_1_obj.GetValue() if self.ignore_ac_in_1_obj else 0
                if ignore == 1:
                    self.ignore_ac_in_1_obj.SetValue(wrap_dbus_value(0))
                    time.sleep(1)
            except:
                pass
            
            target_type = self.DbusSettings['gridInputType']
            target_limit = self.DbusSettings['gridCurrentLimit']
            
            self.ac_input_type_obj.SetValue(wrap_dbus_value(target_type))
            
            if self.current_limit_is_adjustable_obj and self.current_limit_is_adjustable_obj.GetValue() == 1:
                self.current_limit_obj.SetValue(wrap_dbus_value(target_limit))
                self.last_derated_active_limit = target_limit
            
            logging.info("=== Grid transfer complete ===")
            
        except Exception as e:
            logging.error(f"Grid transfer failed: {e}")
        finally:
            self.transfer_state = TransferState.IDLE
            self.transfer_lock.release("transfer_switch")
        
        return False
    
    def update_remote_generator_selected(self):
        """Update RemoteGeneratorSelected"""
        if self.remote_generator_selected_item is None:
            return
        
        new_val = 1 if self.onGenerator else 0
        if new_val != self.remote_generator_selected_local_value:
            try:
                self.remote_generator_selected_item.SetValue(wrap_dbus_value(new_val))
                self.remote_generator_selected_local_value = new_val
            except Exception as e:
                logging.error(f"Could not set RemoteGeneratorSelected: {e}")
    
    def _validate_settings(self):
        """Validate settings"""
        valid = True
        try:
            if self.DbusSettings['gridCurrentLimit'] < 0 or self.DbusSettings['gridCurrentLimit'] > 100:
                logging.error("Grid limit out of range")
                valid = False
            if self.DbusSettings['generatorCurrentLimit'] < 0 or self.DbusSettings['generatorCurrentLimit'] > 100:
                logging.error("Generator limit out of range")
                valid = False
            if self.DbusSettings['gridInputType'] not in (0, 1, 2, 3):
                logging.error("Grid input type invalid")
                valid = False
        except KeyError as e:
            logging.error(f"Missing setting: {e}")
            valid = False
        return valid

def setup_logging():
    logger = logging.getLogger()
    for handler in logger.handlers[:]:
        logger.removeHandler(handler)
    
    formatter = logging.Formatter('%(asctime)s - %(levelname)s - %(message)s')
    console = logging.StreamHandler(sys.stdout)
    console.setFormatter(formatter)
    logger.addHandler(console)
    logger.setLevel(logging.INFO)

def main():
    setup_logging()
    
    logging.info("=" * 60)
    logging.info("External Transfer Switch Monitor With Auto Gen Current starting")
    logging.info("=" * 60)
    
    DynamicTransferSwitch()
    
    GLib.MainLoop().run()

if __name__ == "__main__":
    main()
