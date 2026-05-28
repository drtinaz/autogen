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
import signal
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
    """Atomic lock to prevent concurrent transfers with watchdog timeout"""
    def __init__(self, base_timeout=30, additional_timeout=0):
        """
        Initialize lock with watchdog timeout
        
        Args:
            base_timeout: Base timeout in seconds (default 30)
            additional_timeout: Additional timeout seconds to add (e.g., shutdown timer)
        """
        self._lock = threading.Lock()
        self._is_locked = False
        self._holder = None
        self._lock_time = None
        self._base_timeout = base_timeout
        self._additional_timeout = additional_timeout
        self._watchdog_timeout = base_timeout + additional_timeout
        self._watchdog_timer = None
        logging.info(f"Lock watchdog configured: {self._watchdog_timeout}s (base={base_timeout}s + additional={additional_timeout}s)")
        
    def update_additional_timeout(self, additional_seconds):
        """Update the additional timeout (e.g., when shutdown timer changes)"""
        with self._lock:
            self._additional_timeout = additional_seconds
            old_timeout = self._watchdog_timeout
            self._watchdog_timeout = self._base_timeout + additional_seconds
            logging.info(f"Lock watchdog timeout updated: {old_timeout}s -> {self._watchdog_timeout}s (base={self._base_timeout}s + shutdown={additional_seconds}s)")
            
            if self._is_locked and self._watchdog_timer:
                self._restart_watchdog()
    
    def _restart_watchdog(self):
        """Restart the watchdog timer with current timeout"""
        if self._watchdog_timer:
            try:
                GLib.source_remove(self._watchdog_timer)
            except Exception as e:
                logging.debug(f"Error removing watchdog timer: {e}")
            self._watchdog_timer = None
        
        if self._is_locked and self._holder:
            self._start_watchdog(self._holder)
    
    def _start_watchdog(self, holder):
        """Start watchdog timer for this lock holder"""
        def watchdog_check():
            with self._lock:
                if self._is_locked and self._holder == holder:
                    elapsed = time.time() - self._lock_time
                    logging.error(f"LOCK WATCHDOG TIMEOUT! Lock held by '{holder}' for {elapsed:.1f}s (timeout={self._watchdog_timeout}s)")
                    logging.error(f"Forcing lock release to prevent system hang")
                    self._is_locked = False
                    self._holder = None
                    self._lock_time = None
                    return False
            return False
        
        self._watchdog_timer = GLib.timeout_add_seconds(self._watchdog_timeout, watchdog_check)
    
    def _stop_watchdog(self):
        """Stop the watchdog timer"""
        if self._watchdog_timer:
            try:
                GLib.source_remove(self._watchdog_timer)
            except Exception as e:
                logging.debug(f"Error stopping watchdog: {e}")
            self._watchdog_timer = None
    
    def acquire(self, holder="unknown", timeout=0):
        """Acquire the lock with optional timeout in seconds (0 = non-blocking)"""
        start_time = time.time()
        while True:
            with self._lock:
                if not self._is_locked:
                    self._is_locked = True
                    self._holder = holder
                    self._lock_time = time.time()
                    logging.info(f"Lock acquired by: {holder} (watchdog: {self._watchdog_timeout}s)")
                    self._start_watchdog(holder)
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
                elapsed = time.time() - self._lock_time if self._lock_time else 0
                self._is_locked = False
                self._holder = None
                self._lock_time = None
                self._stop_watchdog()
                logging.info(f"Lock released by: {holder} (held for {elapsed:.1f}s)")
                return True
            elif self._is_locked:
                elapsed = time.time() - self._lock_time if self._lock_time else 0
                logging.warning(f"Cannot release lock - held by '{self._holder}' for {elapsed:.1f}s, requested by '{holder}'")
                return False
            else:
                logging.debug(f"Lock not held, release requested by {holder}")
                return False
    
    def force_release(self, reason="unknown"):
        """Force release the lock (emergency use only)"""
        with self._lock:
            if self._is_locked:
                elapsed = time.time() - self._lock_time if self._lock_time else 0
                logging.error(f"FORCE releasing lock held by '{self._holder}' for {elapsed:.1f}s. Reason: {reason}")
                self._is_locked = False
                self._holder = None
                self._lock_time = None
                self._stop_watchdog()
                return True
            return False
    
    def is_held_by(self, holder):
        with self._lock:
            return self._is_locked and self._holder == holder
    
    def get_holder(self):
        with self._lock:
            return self._holder if self._is_locked else None
    
    def get_hold_duration(self):
        with self._lock:
            if self._is_locked and self._lock_time:
                return time.time() - self._lock_time
            return 0.0
            
    @property
    def is_locked(self):
        with self._lock:
            return self._is_locked
    
    @property
    def watchdog_timeout(self):
        return self._watchdog_timeout

class DynamicTransferSwitch:
    def __init__(self):
        # Setup DBus main loop
        DBusGMainLoop(set_as_default=True)
        self.bus = dbus.SystemBus()
        
        # Setup signal handlers for graceful shutdown
        self._setup_signal_handlers()
        
        # Load configuration
        self._load_and_set_config()
        
        # Initialize lock AFTER config is loaded (so we have SHUTDOWN_TIMER_SECONDS)
        lock_base_timeout = 30
        lock_additional_timeout = getattr(self, 'SHUTDOWN_TIMER_SECONDS', 10)
        self.transfer_lock = AtomicTransferLock(
            base_timeout=lock_base_timeout,
            additional_timeout=lock_additional_timeout
        )
        
        # Transfer switch state
        self.onGenerator = False
        self.lastOnGenerator = None
        self.transfer_state = TransferState.IDLE
        
        # Startup synchronization
        self.startup_sync_complete = False
        self.startup_sequence_run = False
        self.startup_step = 0  # Track startup progress
        
        # Service discovery with backoff
        self.discovery_attempts = 0
        self.consecutive_failures = 0
        self.max_consecutive_failures = 10
        self.discovery_backoff_base = 30
        self.discovery_backoff_max = 300
        self.discovery_retry_timer = None
        
        # VE.Bus direct objects
        self.vebus_service = None
        self.number_of_ac_inputs = None
        self.ac_input_type_obj = None
        self.current_limit_obj = None
        self.current_limit_is_adjustable_obj = None
        self.ignore_ac_in_1_obj = None
        self.remote_generator_selected_item = None
        self.remote_generator_selected_local_value = -1
        
        # Signal match tracking with cleanup
        self.active_matches = {}
        self.items_matches = {}
        self.properties_matches = {}  # For PropertiesChanged subscriptions
        
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
        
        # Lists of services to monitor with ItemsChanged
        self.items_changed_services = {}
        
        # Sensor values with tracking for threshold detection
        self.outdoor_temp_fahrenheit = self.DEFAULT_OUTDOOR_TEMP_F
        self.altitude_feet = self.DEFAULT_ALTITUDE_FEET
        self.generator_temp_fahrenheit = self.DEFAULT_GENERATOR_TEMP_F
        self.gen_auto_current_state = None
        self.previous_gen_auto_current_state = None
        
        # Track last raw sensor values for threshold comparison
        self.last_outdoor_temp_raw = self.DEFAULT_OUTDOOR_TEMP_F
        self.last_altitude_feet_raw = self.DEFAULT_ALTITUDE_FEET
        self.last_generator_temp_raw = self.DEFAULT_GENERATOR_TEMP_F
        
        # Service discovery state
        self.transferSwitchActive = False
        self.transferSwitchLocation = 0
        self.initial_derated_output_logged = False
        
        # Track last derated value to avoid unnecessary writes
        self.last_derated_active_limit = None
        self.last_derated_gen_setting = None
        
        # Debounce tracking
        self._last_derate_time = 0
        self._derating_pending = False
        
        # Service patterns from config
        self.generator_temp_patterns = ["gen", "generator", "gen temp", "generator temp"]
        self.transfer_switch_pattern = "transfer switch"
        self.gen_auto_current_pattern = "gen auto current"
        self.outdoor_temp_pattern = "outdoor"
        
        # Setup D-Bus settings
        self._setup_settings()
        
        # Setup NameOwnerChanged monitoring for all services
        self.bus.add_signal_receiver(
            self._on_name_owner_changed,
            bus_name="org.freedesktop.DBus",
            dbus_interface="org.freedesktop.DBus",
            signal_name="NameOwnerChanged"
        )
        
        # Start service discovery
        GLib.idle_add(self._discover_services)
        
        # Add periodic lock health monitoring
        GLib.timeout_add_seconds(60, self._monitor_lock_health)
        
        # Add periodic status reporting (every 300 seconds - 5 minutes)
        GLib.timeout_add_seconds(900, self._periodic_status)
    
    def _setup_signal_handlers(self):
        """Setup signal handlers for graceful shutdown"""
        def signal_handler(signum, frame):
            logging.info(f"Signal {signum} received, shutting down gracefully...")
            self._cleanup()
            sys.exit(0)
        
        signal.signal(signal.SIGTERM, signal_handler)
        signal.signal(signal.SIGINT, signal_handler)
        signal.signal(signal.SIGHUP, self._reload_config)
    
    def _reload_config(self, signum, frame):
        """Reload configuration on SIGHUP"""
        logging.info(f"Signal {signum} received, reloading configuration...")
        try:
            old_shutdown_timer = self.SHUTDOWN_TIMER_SECONDS
            self._load_and_set_config()
            
            # Update lock timeout if shutdown timer changed
            if hasattr(self, 'transfer_lock') and self.SHUTDOWN_TIMER_SECONDS != old_shutdown_timer:
                self.transfer_lock.update_additional_timeout(self.SHUTDOWN_TIMER_SECONDS)
                logging.info(f"Configuration reloaded: shutdown timer {old_shutdown_timer}s -> {self.SHUTDOWN_TIMER_SECONDS}s")
            else:
                logging.info("Configuration reloaded successfully")
        except Exception as e:
            logging.error(f"Failed to reload configuration: {e}")
    
    def _cleanup(self):
        """Clean up D-Bus matches and resources"""
        logging.info("Cleaning up D-Bus signal matches...")
        
        for key, match in self.active_matches.items():
            try:
                match.remove()
            except Exception as e:
                logging.debug(f"Error removing match {key}: {e}")
        self.active_matches.clear()
        
        for service, match in self.items_matches.items():
            try:
                match.remove()
            except Exception as e:
                logging.debug(f"Error removing ItemsChanged match {service}: {e}")
        self.items_matches.clear()
        
        # Clean up PropertiesChanged matches
        for service, match in self.properties_matches.items():
            try:
                match.remove()
            except Exception as e:
                logging.debug(f"Error removing PropertiesChanged match {service}: {e}")
        self.properties_matches.clear()
        
        if self.discovery_retry_timer:
            try:
                GLib.source_remove(self.discovery_retry_timer)
            except Exception as e:
                logging.debug(f"Error removing discovery timer: {e}")
        
        logging.info("Cleanup complete")
    
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
        
        self._subscribe_to_saved_limits()
    
    def _on_settings_device_changed(self, setting, old_value, new_value):
        """SettingsDevice callback"""
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
        self.ALTITUDE_THRESHOLD_FEET = 50.0  # Configurable altitude threshold to trigger a derate calculation
        self.SENSOR_CHANGE_THRESHOLD = 0.5  # threshold for temperature sensors to trigger a derate calculation
        
        # Service patterns (can be overridden in config)
        self.generator_temp_patterns = ["gen", "generator", "gen temp", "generator temp"]
        self.transfer_switch_pattern = "transfer switch"
        self.gen_auto_current_pattern = "gen auto current"
        self.outdoor_temp_pattern = "outdoor"
        
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
            
            # Load altitude threshold from config
            if config.has_section('SensorThresholds'):
                self.ALTITUDE_THRESHOLD_FEET = config.getfloat('SensorThresholds', 'altitude_threshold_feet', fallback=self.ALTITUDE_THRESHOLD_FEET)
                logging.info(f"Altitude threshold: {self.ALTITUDE_THRESHOLD_FEET}ft")
                self.SENSOR_CHANGE_THRESHOLD = config.getfloat('SensorThresholds', 'sensor_change_threshold', fallback=self.SENSOR_CHANGE_THRESHOLD)
                logging.info(f"Temperature threshold: {self.SENSOR_CHANGE_THRESHOLD}")
            
            # Load service patterns from config
            if config.has_section('ServicePatterns'):
                # Generator temp patterns - parse comma-separated list
                patterns_str = config.get('ServicePatterns', 'generator_temp_patterns', fallback=None)
                if patterns_str:
                    self.generator_temp_patterns = [p.strip().lower() for p in patterns_str.split(',')]
                    logging.debug(f"Generator temp patterns: {self.generator_temp_patterns}")
                
                self.transfer_switch_pattern = config.get('ServicePatterns', 'transfer_switch_pattern', fallback=self.transfer_switch_pattern).lower()
                self.gen_auto_current_pattern = config.get('ServicePatterns', 'gen_auto_current_pattern', fallback=self.gen_auto_current_pattern).lower()
                self.outdoor_temp_pattern = config.get('ServicePatterns', 'outdoor_temp_pattern', fallback=self.outdoor_temp_pattern).lower()
            
            if config.has_section('TransferSwitchSettings'):
                new_shutdown_timer = config.getfloat('TransferSwitchSettings', 'shutdown_timer', fallback=self.SHUTDOWN_TIMER_SECONDS)
                # Validate shutdown timer - limit to 5-120 seconds
                if new_shutdown_timer < 5:
                    logging.warning(f"Shutdown timer {new_shutdown_timer}s is below minimum 5s, setting to 5s")
                    new_shutdown_timer = 5
                elif new_shutdown_timer > 120:
                    logging.warning(f"Shutdown timer {new_shutdown_timer}s exceeds maximum 120s, setting to 120s")
                    new_shutdown_timer = 120
                
                if new_shutdown_timer != self.SHUTDOWN_TIMER_SECONDS:
                    self.SHUTDOWN_TIMER_SECONDS = new_shutdown_timer
                    if hasattr(self, 'transfer_lock'):
                        self.transfer_lock.update_additional_timeout(self.SHUTDOWN_TIMER_SECONDS)
                    logging.info(f"Generator shutdown timer: {self.SHUTDOWN_TIMER_SECONDS}s")
            
            logging.info(f"Lock watchdog timeout: 30s + {self.SHUTDOWN_TIMER_SECONDS}s = {30 + self.SHUTDOWN_TIMER_SECONDS}s")
            logging.debug(f"Derating constants: BaseTemp={self.BASE_TEMPERATURE_THRESHOLD_F}F, TempCoeff={self.TEMP_COEFFICIENT}, AltCoeff={self.ALTITUDE_COEFFICIENT}")
            logging.debug(f"Generator: BaseAmps={self.BASE_GENERATOR_OUTPUT_AMPS}A, Buffer={self.OUTPUT_BUFFER}")
            
        except (configparser.Error, ValueError) as e:
            logging.error(f"Error reading config: {e}")
    
    def _subscribe_to_saved_limits(self):
        """Subscribe to saved current limit changes using PropertiesChanged"""
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
                logging.debug(f"Subscribed to generator current limit")
            except Exception as e:
                logging.error(f"Failed to subscribe to generator limit: {e}")
        
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
                logging.debug(f"Subscribed to grid current limit")
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
            logging.debug(f"Subscribed to active current limit on {service_name}")
            self._read_initial_active_limit()
            return True
        except Exception as e:
            logging.error(f"Failed to subscribe to active limit: {e}")
            return False
    
    def _read_initial_active_limit(self):
        """Read initial active current limit value"""
        if self.vebus_service:
            try:
                obj = self.bus.get_object(self.vebus_service, AC_ACTIVE_INPUT_CURRENT_LIMIT_PATH)
                iface = dbus.Interface(obj, BUS_ITEM_INTERFACE)
                value = iface.GetValue()
                logging.info(f"Initial active current limit: {value}A")
                self._handle_active_limit_change(float(value))
            except Exception as e:
                logging.error(f"Failed to read initial active limit: {e}")
    
    def _register_items_changed_service(self, service_name, service_type, value_callback):
        """Register a service to monitor with appropriate signal types"""
        if service_name in self.items_changed_services:
            return
        
        logging.debug(f"Registering service: {service_name} (type: {service_type})")
        self.items_changed_services[service_name] = {
            'type': service_type,
            'callback': value_callback
        }
        
        if self.bus.name_has_owner(service_name):
            # For temperature sensors, subscribe to BOTH signal types for compatibility
            if service_type in ['outdoor_temp', 'generator_temp']:
                self._subscribe_items_changed(service_name)      # For ItemsChanged
                self._subscribe_properties_changed(service_name)  # For PropertiesChanged
            else:
                self._subscribe_items_changed(service_name)
    
    def _subscribe_items_changed(self, service_name):
        """Subscribe to ItemsChanged signals for a specific service"""
        if service_name in self.items_matches:
            return
        
        try:
            match = self.bus.add_signal_receiver(
                lambda items, **kwargs: self._on_items_changed(items, kwargs, service_name),
                bus_name=service_name,
                path="/",
                dbus_interface="com.victronenergy.BusItem",
                signal_name="ItemsChanged",
                sender_keyword='sender_name'
            )
            self.items_matches[service_name] = match
            logging.debug(f"ItemsChanged subscribed: {service_name}")
            return True
        except Exception as e:
            logging.error(f"Failed to subscribe ItemsChanged for {service_name}: {e}")
            return False
    
    def _subscribe_properties_changed(self, service_name):
        """Subscribe to PropertiesChanged signals for a specific service"""
        if service_name in self.properties_matches:
            return
        
        # Subscribe to PropertiesChanged on all paths, filter in handler
        try:
            match = self.bus.add_signal_receiver(
                lambda *args, **kwargs: self._on_properties_changed(*args, **kwargs, service_name=service_name),
                bus_name=service_name,
                dbus_interface="com.victronenergy.BusItem",
                signal_name="PropertiesChanged",
                path_keyword='path',  # This puts the path in kwargs['path']
                sender_keyword='sender_name'
            )
            self.properties_matches[service_name] = match
            logging.debug(f"PropertiesChanged subscribed for {service_name}")
            return True
        except Exception as e:
            logging.debug(f"Could not subscribe PropertiesChanged for {service_name}: {e}")
            return False
    
    def _unsubscribe_items_changed(self, service_name):
        """Unsubscribe from ItemsChanged signals for a service"""
        if service_name in self.items_matches:
            try:
                self.items_matches[service_name].remove()
                del self.items_matches[service_name]
                logging.debug(f"ItemsChanged unsubscribed: {service_name}")
            except Exception as e:
                logging.error(f"Failed to unsubscribe: {e}")
    
    def _unsubscribe_properties_changed(self, service_name):
        """Unsubscribe from PropertiesChanged signals for a service"""
        if service_name in self.properties_matches:
            try:
                self.properties_matches[service_name].remove()
                del self.properties_matches[service_name]
                logging.debug(f"PropertiesChanged unsubscribed: {service_name}")
            except Exception as e:
                logging.error(f"Failed to unsubscribe: {e}")
    
    def _on_items_changed(self, items, kwargs, service_name):
        """Handle ItemsChanged signals"""
        if service_name not in self.items_changed_services:
            return
        
        if not self.startup_sync_complete:
            return
        
        service_info = self.items_changed_services[service_name]
        
        if not isinstance(items, dict):
            return
        
        for path, changes in items.items():
            if 'Value' in changes:
                try:
                    service_info['callback'](path, changes['Value'])
                except Exception as e:
                    logging.error(f"Error in ItemsChanged callback: {e}")
    
    def _on_properties_changed(self, *args, **kwargs):
        """Handle PropertiesChanged signals for temperature sensors - ONLY process /Temperature path"""
        service_name = kwargs.get('service_name')
        if not service_name or service_name not in self.items_changed_services:
            return
        
        if not self.startup_sync_complete:
            return
        
        # Get the path from kwargs (set by path_keyword='path')
        path = kwargs.get('path')
        
        # ONLY process Temperature path, ignore RawValue and others
        if path != TEMPERATURE_PATH:
            logging.debug(f"PropertiesChanged ignoring {service_name} path: {path} (only processing {TEMPERATURE_PATH})")
            return
        
        if args and len(args) > 0:
            changes = args[0]
            if isinstance(changes, dict) and 'Value' in changes:
                value = changes['Value']
                service_info = self.items_changed_services[service_name]
                logging.debug(f"PropertiesChanged for {service_name} - Temperature = {value}")
                service_info['callback'](path, value)
    
    def _on_name_owner_changed(self, name, old_owner, new_owner):
        """Handle service appearance/disappearance with enhanced logging"""
        
        if name.startswith(VEBUS_SERVICE_BASE):
            if new_owner and not old_owner:
                logging.info(f"VE.Bus connected: {name}")
                self._subscribe_to_active_limit(name)
                if not self.vebus_service:
                    self.vebus_service = name
                    self._setup_vebus_objects()
            elif old_owner and not new_owner:
                logging.warning(f"VE.Bus disconnected: {name}")
                # Store last known active limit before disconnect
                if self.last_derated_active_limit is not None:
                    logging.info(f"  Last known active limit: {self.last_derated_active_limit}A")
                key = f"{name}{AC_ACTIVE_INPUT_CURRENT_LIMIT_PATH}"
                if key in self.active_matches:
                    try:
                        self.active_matches[key].remove()
                        del self.active_matches[key]
                    except Exception as e:
                        logging.debug(f"Error removing VE.Bus match: {e}")
                if self.vebus_service == name:
                    self.vebus_service = None
        
        elif name == SETTINGS_SERVICE_NAME:
            if new_owner and not old_owner:
                logging.info(f"Settings service connected: {name}")
                self._subscribe_to_saved_limits()
            elif old_owner and not new_owner:
                logging.warning(f"Settings service disconnected: {name}")
                for key in list(self.active_matches.keys()):
                    if SETTINGS_SERVICE_NAME in key:
                        try:
                            self.active_matches[key].remove()
                            del self.active_matches[key]
                        except Exception as e:
                            logging.debug(f"Error removing settings match: {e}")
        
        elif name in self.items_changed_services:
            if new_owner and not old_owner:
                logging.info(f"Service online: {name}")
                
                # Get service type and last known value before reconnection
                service_info = self.items_changed_services[name]
                service_type = service_info.get('type', 'unknown')
                
                # Store last known value based on service type - use current values
                last_value = None
                if service_type == 'outdoor_temp':
                    last_value = self.outdoor_temp_fahrenheit
                    logging.info(f"  Last known outdoor temp: {last_value:.1f}F")
                elif service_type == 'generator_temp':
                    last_value = self.generator_temp_fahrenheit
                    logging.info(f"  Last known generator temp: {last_value:.1f}F")
                elif service_type == 'gps':
                    # Use the current altitude value before disconnect for comparison
                    last_value = self.altitude_feet
                    logging.info(f"  Last known altitude: {last_value:.0f}ft")
                elif service_type == 'transfer_switch':
                    last_value = self.onGenerator
                    logging.info(f"  Last known transfer state: {'GENERATOR' if last_value else 'GRID'}" if last_value is not None else "  No previous transfer state")
                elif service_type == 'gen_auto_current':
                    last_value = self.gen_auto_current_state
                    logging.info(f"  Last known Gen Auto state: {'ON' if last_value == GEN_AUTO_CURRENT_ON else 'OFF'}" if last_value is not None else "  No previous Gen Auto state")
                
                # Store the last value in the service info dict for use in the callback
                self.items_changed_services[name]['last_known_value'] = last_value
                
                # Re-subscribe to appropriate signals
                if service_type in ['outdoor_temp', 'generator_temp']:
                    self._subscribe_items_changed(name)
                    self._subscribe_properties_changed(name)
                else:
                    self._subscribe_items_changed(name)
                
                # Schedule reading of new values after reconnection
                GLib.timeout_add_seconds(1, lambda: self._read_initial_items_changed_values_with_logging(name, service_type, last_value))
                
            elif old_owner and not new_owner:
                logging.warning(f"Service offline: {name}")
                
                # Log the last known value before disconnect
                service_info = self.items_changed_services.get(name, {})
                service_type = service_info.get('type', 'unknown')
                
                if service_type == 'outdoor_temp':
                    logging.info(f"  Last known outdoor temp before disconnect: {self.outdoor_temp_fahrenheit:.1f}F")
                elif service_type == 'generator_temp':
                    logging.info(f"  Last known generator temp before disconnect: {self.generator_temp_fahrenheit:.1f}F")
                elif service_type == 'gps':
                    logging.info(f"  Last known altitude before disconnect: {self.altitude_feet:.0f}ft")
                elif service_type == 'transfer_switch':
                    logging.info(f"  Last known transfer state before disconnect: {'GENERATOR' if self.onGenerator else 'GRID'}")
                elif service_type == 'gen_auto_current':
                    logging.info(f"  Last known Gen Auto state before disconnect: {'ON' if self.gen_auto_current_state == GEN_AUTO_CURRENT_ON else 'OFF'}")
                
                self._unsubscribe_items_changed(name)
                if service_type in ['outdoor_temp', 'generator_temp']:
                    self._unsubscribe_properties_changed(name)
    
    def _read_initial_items_changed_values_with_logging(self, service_name, service_type, last_value):
        """Read initial values after service reconnection and compare with last known value"""
        if service_name not in self.items_changed_services:
            return
        
        try:
            # Try to read the specific path based on service type
            if service_type == 'outdoor_temp':
                try:
                    temp_obj = self.bus.get_object(service_name, TEMPERATURE_PATH)
                    temp_iface = dbus.Interface(temp_obj, BUS_ITEM_INTERFACE)
                    temp_c = temp_iface.GetValue()
                    if temp_c is not None:
                        new_temp_f = (temp_c * 9/5) + 32
                        logging.info(f"New outdoor temp reading: {new_temp_f:.1f}F")
                        if last_value is not None:
                            diff = new_temp_f - last_value
                            logging.info(f"  Change from last known: {diff:+.1f}F")
                            if abs(diff) >= self.SENSOR_CHANGE_THRESHOLD:
                                logging.info(f"  → Significant change, triggering derating")
                            else:
                                logging.info(f"  → No significant change (threshold: {self.SENSOR_CHANGE_THRESHOLD}F)")
                        self.outdoor_temp_fahrenheit = new_temp_f
                        self.last_outdoor_temp_raw = new_temp_f
                        GLib.idle_add(self._trigger_derating)
                except Exception as e:
                    logging.debug(f"Could not read temp after reconnection: {e}")
                    
            elif service_type == 'generator_temp':
                try:
                    temp_obj = self.bus.get_object(service_name, TEMPERATURE_PATH)
                    temp_iface = dbus.Interface(temp_obj, BUS_ITEM_INTERFACE)
                    temp_c = temp_iface.GetValue()
                    if temp_c is not None:
                        new_temp_f = (temp_c * 9/5) + 32
                        logging.info(f"New generator temp reading: {new_temp_f:.1f}F")
                        if last_value is not None:
                            diff = new_temp_f - last_value
                            logging.info(f"  Change from last known: {diff:+.1f}F")
                            if abs(diff) >= self.SENSOR_CHANGE_THRESHOLD:
                                logging.info(f"  → Significant change, triggering derating")
                            else:
                                logging.info(f"  → No significant change (threshold: {self.SENSOR_CHANGE_THRESHOLD}F)")
                        self.generator_temp_fahrenheit = new_temp_f
                        self.last_generator_temp_raw = new_temp_f
                        GLib.idle_add(self._trigger_derating)
                except Exception as e:
                    logging.debug(f"Could not read temp after reconnection: {e}")
                    
            elif service_type == 'gps':
                try:
                    alt_obj = self.bus.get_object(service_name, ALTITUDE_PATH)
                    alt_iface = dbus.Interface(alt_obj, BUS_ITEM_INTERFACE)
                    alt = alt_iface.GetValue()
                    if alt is not None:
                        if isinstance(alt, dbus.Array):
                            alt_m = float(alt[0]) if alt else None
                        else:
                            alt_m = float(alt)
                        if alt_m is not None:
                            new_alt_ft = alt_m * 3.28084
                            logging.info(f"New altitude reading: {new_alt_ft:.0f}ft")
                            if last_value is not None:
                                diff = new_alt_ft - last_value
                                logging.info(f"  Change from last known: {diff:+.0f}ft")
                                if abs(diff) >= self.ALTITUDE_THRESHOLD_FEET:
                                    logging.info(f"  → Significant change, triggering derating")
                                else:
                                    logging.info(f"  → No significant change (threshold: {self.ALTITUDE_THRESHOLD_FEET}ft)")
                            # Update the current altitude value
                            self.altitude_feet = new_alt_ft
                            self.last_altitude_feet_raw = new_alt_ft
                            GLib.idle_add(self._trigger_derating)
                except Exception as e:
                    logging.debug(f"Could not read altitude after reconnection: {e}")
                    
            elif service_type == 'transfer_switch':
                try:
                    state_obj = self.bus.get_object(service_name, STATE_PATH)
                    state_iface = dbus.Interface(state_obj, BUS_ITEM_INTERFACE)
                    state = state_iface.GetValue()
                    if state is not None:
                        new_on_generator = state in GENERATOR_ON_VALUE
                        logging.info(f"New transfer switch state: {'GENERATOR' if new_on_generator else 'GRID'}")
                        if last_value is not None:
                            logging.info(f"  Previous state: {'GENERATOR' if last_value else 'GRID'}")
                            if new_on_generator != last_value:
                                logging.info(f"  → State changed during disconnect!")
                        self.onGenerator = new_on_generator
                except Exception as e:
                    logging.debug(f"Could not read transfer state after reconnection: {e}")
                    
            elif service_type == 'gen_auto_current':
                try:
                    state_obj = self.bus.get_object(service_name, STATE_PATH)
                    state_iface = dbus.Interface(state_obj, BUS_ITEM_INTERFACE)
                    state = state_iface.GetValue()
                    if state is not None:
                        new_state = int(state)
                        logging.info(f"New Gen Auto state: {'ON' if new_state == GEN_AUTO_CURRENT_ON else 'OFF'}")
                        if last_value is not None:
                            logging.info(f"  Previous state: {'ON' if last_value == GEN_AUTO_CURRENT_ON else 'OFF'}")
                            if new_state != last_value:
                                logging.info(f"  → State changed during disconnect!")
                        self.gen_auto_current_state = new_state
                        if new_state == GEN_AUTO_CURRENT_ON:
                            GLib.idle_add(self._force_derating)
                except Exception as e:
                    logging.debug(f"Could not read Gen Auto state after reconnection: {e}")
                    
        except Exception as e:
            logging.debug(f"Could not read initial values from {service_name}: {e}")
    
    def _read_initial_items_changed_values(self, service_name):
        """Read initial values after service reconnection"""
        if service_name not in self.items_changed_services:
            return
        
        try:
            obj = self.bus.get_object(service_name, "/")
            logging.debug(f"Reconnected to {service_name}, waiting for initial values")
        except Exception as e:
            logging.debug(f"Could not read initial values from {service_name}: {e}")
    
    def _discover_services(self):
        """Discover all required services with exponential backoff"""
        self.discovery_attempts += 1
        logging.debug(f"Service discovery attempt {self.discovery_attempts}")
        
        if not self.vebus_found:
            if self._find_vebus_service():
                self.vebus_found = True
        
        if not self.transfer_switch_found:
            if self._find_transfer_switch_input():
                self.transfer_switch_found = True
        
        if not self.outdoor_temp_found:
            if self._find_outdoor_temperature_sensor():
                self.outdoor_temp_found = True
        
        if not self.generator_temp_found:
            if self._find_generator_temperature_sensor():
                self.generator_temp_found = True
        
        if not self.gps_found:
            if self._find_gps_service():
                self.gps_found = True
        
        if not self.gen_auto_current_found:
            if self._find_gen_auto_current_input():
                self.gen_auto_current_found = True
        
        required_missing = []
        if not self.vebus_found:
            required_missing.append("VE.Bus")
        if not self.transfer_switch_found:
            required_missing.append("Transfer Switch")
        
        optional_missing = []
        if not self.outdoor_temp_found:
            optional_missing.append("outdoor_temp")
        if not self.generator_temp_found:
            optional_missing.append("generator_temp")
        if not self.gps_found:
            optional_missing.append("gps")
        if not self.gen_auto_current_found:
            optional_missing.append("gen_auto_current")
        
        if required_missing:
            self.consecutive_failures += 1
            delay = min(self.discovery_backoff_max, 
                       self.discovery_backoff_base * (2 ** min(self.consecutive_failures - 1, 5)))
            
            logging.warning(f"Required services missing: {', '.join(required_missing)} - retrying in {delay}s")
            
            if self.consecutive_failures >= self.max_consecutive_failures:
                logging.error(f"Max consecutive failures ({self.max_consecutive_failures}) reached")
            
            self.discovery_retry_timer = GLib.timeout_add_seconds(delay, self._discover_services)
            return
        
        self.consecutive_failures = 0
        
        # Only start startup sync if not already complete or in progress
        if not self.startup_sync_complete and not self.startup_sequence_run:
            self._start_startup_sync()
        
        if optional_missing:
            opt_delay = min(120, self.discovery_backoff_base * (2 ** min(self.consecutive_failures, 3)))
            logging.info(f"Still looking for optional services: {', '.join(optional_missing)} - retrying in {opt_delay}s")
            self.discovery_retry_timer = GLib.timeout_add_seconds(opt_delay, self._discover_services)
        else:
            logging.info("All services discovered - stopping discovery")
            if self.discovery_retry_timer:
                GLib.source_remove(self.discovery_retry_timer)
                self.discovery_retry_timer = None
    
    def _start_startup_sync(self):
        """Start non-blocking startup synchronization"""
        if self.startup_sync_complete or self.startup_sequence_run:
            logging.debug("Startup already in progress or complete, ignoring")
            return
        
        logging.info("Starting startup synchronization (non-blocking)")
        self.startup_sequence_run = True
        self.startup_step = 0
        GLib.timeout_add(100, self._continue_startup)
    
    def _continue_startup(self):
        """Continue startup synchronization in steps (non-blocking)"""
        
        # Prevent continuation if startup is already complete
        if self.startup_sync_complete:
            logging.debug("Startup already complete, ignoring continuation")
            return False
        
        if self.startup_step == 0:
            logging.debug("Startup step 1: Reading transfer switch state")
            if self.transfer_switch_service:
                try:
                    obj = self.bus.get_object(self.transfer_switch_service, STATE_PATH)
                    iface = dbus.Interface(obj, BUS_ITEM_INTERFACE)
                    state = iface.GetValue()
                    if state in (12, 3):
                        self.onGenerator = True
                    elif state in (13, 2):
                        self.onGenerator = False
                    logging.info(f"Transfer Switch: {'GENERATOR' if self.onGenerator else 'GRID/SHORE'}")
                except Exception as e:
                    logging.error(f"Failed to read transfer switch state: {e}")
            self.startup_step = 1
            GLib.timeout_add(100, self._continue_startup)
            return True
        
        elif self.startup_step == 1:
            logging.debug("Startup step 2: Reading AC state")
            try:
                current_input_type = self.ac_input_type_obj.GetValue()
                current_limit = self.current_limit_obj.GetValue() if self.current_limit_obj else None
                logging.info(f"Current AC Input: {current_input_type}")
                logging.info(f"Current Active Limit: {current_limit}A")
            except Exception as e:
                logging.error(f"Failed to read AC state: {e}")
                self.startup_sync_complete = True
                return False
            
            saved_grid_limit = self.DbusSettings['gridCurrentLimit']
            saved_gen_limit = self.DbusSettings['generatorCurrentLimit']
            saved_grid_type = self.DbusSettings['gridInputType']
            
            logging.info(f"Saved Grid Limit: {saved_grid_limit}A")
            logging.info(f"Saved Generator Limit: {saved_gen_limit}A")
            
            self.startup_step = 2
            self.saved_grid_limit = saved_grid_limit
            self.saved_gen_limit = saved_gen_limit
            self.saved_grid_type = saved_grid_type
            self.current_input_type = current_input_type
            GLib.timeout_add(100, self._continue_startup)
            return True
        
        elif self.startup_step == 2:
            logging.debug("Startup step 3: Applying settings")
            if self.onGenerator:
                if self.current_input_type != 2:
                    logging.info("Applying generator settings...")
                    try:
                        self.ac_input_type_obj.SetValue(wrap_dbus_value(2))
                        if self.current_limit_is_adjustable_obj and self.current_limit_is_adjustable_obj.GetValue() == 1:
                            self.current_limit_obj.SetValue(wrap_dbus_value(self.saved_gen_limit))
                        logging.info("Generator settings applied")
                    except Exception as e:
                        logging.error(f"Failed to apply generator settings: {e}")
            else:
                if self.current_input_type != self.saved_grid_type:
                    logging.info("Applying grid/shore settings...")
                    try:
                        self.ac_input_type_obj.SetValue(wrap_dbus_value(self.saved_grid_type))
                        if self.current_limit_is_adjustable_obj and self.current_limit_is_adjustable_obj.GetValue() == 1:
                            self.current_limit_obj.SetValue(wrap_dbus_value(self.saved_grid_limit))
                        logging.info("Grid/Shore settings applied")
                    except Exception as e:
                        logging.error(f"Failed to apply grid settings: {e}")
            
            # Set completion flags before logging to prevent race conditions
            self.startup_sync_complete = True
            self.startup_sequence_run = True
            
            logging.info("=" * 60)
            logging.info("STARTUP COMPLETE - Normal operations")
            logging.info("=" * 60)
            
            # Trigger derating after startup (non-blocking)
            GLib.idle_add(self._trigger_derating)
            return False  # Stop the timeout chain
        
        return False
    
    def _find_vebus_service(self):
        """Find VE.Bus service"""
        services = [name for name in self.bus.list_names() if name.startswith(VEBUS_SERVICE_BASE)]
        if services:
            self.vebus_service = services[0]
            self._setup_vebus_objects()
            self._subscribe_to_active_limit(self.vebus_service)
            logging.info(f"Found VE.Bus: {self.vebus_service}")
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
            logging.debug(f"Current limit adjustable: {is_adjustable}")
            
            try:
                self.remote_generator_selected_item = self.bus.get_object(self.vebus_service, REMOTE_GENERATOR_SELECTED_PATH)
            except dbus.DBusException as e:
                logging.debug(f"RemoteGeneratorSelected not available: {e}")
                self.remote_generator_selected_item = None
            
            if self.number_of_ac_inputs == 2:
                ac_input_path = AC_INPUT_2_PATH
            else:
                ac_input_path = AC_INPUT_1_PATH
            
            self.ac_input_type_obj = self.bus.get_object(SETTINGS_SERVICE_NAME, ac_input_path)
            logging.debug(f"AC input type path: {ac_input_path}")
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
                    if name and self.transfer_switch_pattern in name.lower():
                        self.transfer_switch_service = service
                        self.transferSwitchActive = True
                        
                        self._register_items_changed_service(
                            service,
                            'transfer_switch',
                            self._on_transfer_switch_value
                        )
                        
                        logging.info(f"Found transfer switch: {service}")
                        return True
                except dbus.DBusException as e:
                    # Expected for services without BusItem interface
                    if "UnknownObject" not in str(e) and "doesn't exist" not in str(e):
                        logging.debug(f"Error checking service {service}: {e}")
                    continue
                except Exception as e:
                    logging.debug(f"Unexpected error checking service {service}: {e}")
                    continue
        return False
    
    def _find_gen_auto_current_input(self):
        """Find digital input for Gen Auto Current"""
        for service in self.bus.list_names():
            if service.startswith(DIGITAL_INPUT_SERVICE_BASE):
                try:
                    obj = self.bus.get_object(service, PRODUCT_NAME_PATH)
                    name = dbus.Interface(obj, BUS_ITEM_INTERFACE).GetValue()
                    if name and self.gen_auto_current_pattern in name.lower():
                        self.gen_auto_current_service = service
                        
                        self._register_items_changed_service(
                            service,
                            'gen_auto_current',
                            self._on_gen_auto_current_value
                        )
                        
                        try:
                            state_obj = self.bus.get_object(service, STATE_PATH)
                            state_iface = dbus.Interface(state_obj, BUS_ITEM_INTERFACE)
                            state = state_iface.GetValue()
                            if state is not None:
                                self.gen_auto_current_state = int(state)
                                logging.info(f"Found Gen Auto Current: {service} - Initial state: {'ON' if self.gen_auto_current_state == GEN_AUTO_CURRENT_ON else 'OFF'}")
                                
                                if self.gen_auto_current_state == GEN_AUTO_CURRENT_ON:
                                    logging.info("Gen Auto Current enabled - forcing derating")
                                    GLib.idle_add(self._force_derating)
                        except dbus.DBusException as e:
                            logging.error(f"Failed to read initial Gen Auto state: {e}")
                        
                        return True
                except dbus.DBusException as e:
                    # Expected for services without BusItem interface
                    if "UnknownObject" not in str(e) and "doesn't exist" not in str(e):
                        logging.debug(f"Error checking service {service}: {e}")
                    continue
                except Exception as e:
                    logging.debug(f"Unexpected error checking service {service}: {e}")
                    continue
        return False
    
    def _find_outdoor_temperature_sensor(self):
        """Find temperature sensor with configured pattern in custom name"""
        for service in self.bus.list_names():
            if service.startswith(TEMPERATURE_SERVICE_BASE):
                try:
                    obj = self.bus.get_object(service, CUSTOM_NAME_PATH)
                    name = dbus.Interface(obj, BUS_ITEM_INTERFACE).GetValue()
                    if name and self.outdoor_temp_pattern in name.lower():
                        self.outdoor_temp_service = service
                        
                        self._register_items_changed_service(
                            service,
                            'outdoor_temp',
                            self._on_outdoor_temp_value
                        )
                        
                        logging.info(f"Found outdoor temp sensor: {service}")
                        
                        try:
                            temp_obj = self.bus.get_object(service, TEMPERATURE_PATH)
                            temp_iface = dbus.Interface(temp_obj, BUS_ITEM_INTERFACE)
                            temp_c = temp_iface.GetValue()
                            if temp_c is not None:
                                self.outdoor_temp_fahrenheit = (temp_c * 9/5) + 32
                                self.last_outdoor_temp_raw = self.outdoor_temp_fahrenheit
                                logging.info(f"Initial outdoor temp: {self.outdoor_temp_fahrenheit:.1f}F")
                                GLib.idle_add(self._trigger_derating)
                        except dbus.DBusException as e:
                            logging.error(f"Failed to read initial temp: {e}")
                        
                        return True
                except dbus.DBusException as e:
                    # Expected for services without BusItem interface
                    if "UnknownObject" not in str(e) and "doesn't exist" not in str(e):
                        logging.debug(f"Error checking service {service}: {e}")
                    continue
                except Exception as e:
                    logging.debug(f"Unexpected error checking service {service}: {e}")
                    continue
        return False
    
    def _find_generator_temperature_sensor(self):
        """Find temperature sensor for generator using configured patterns"""
        for service in self.bus.list_names():
            if service.startswith(TEMPERATURE_SERVICE_BASE):
                try:
                    obj = self.bus.get_object(service, CUSTOM_NAME_PATH)
                    name = dbus.Interface(obj, BUS_ITEM_INTERFACE).GetValue()
                    if name:
                        name_lower = name.lower()
                        for pattern in self.generator_temp_patterns:
                            if pattern in name_lower:
                                self.generator_temp_service = service
                                
                                self._register_items_changed_service(
                                    service,
                                    'generator_temp',
                                    self._on_generator_temp_value
                                )
                                
                                logging.info(f"Found generator temp sensor: {service} (matched pattern: {pattern})")
                                
                                try:
                                    temp_obj = self.bus.get_object(service, TEMPERATURE_PATH)
                                    temp_iface = dbus.Interface(temp_obj, BUS_ITEM_INTERFACE)
                                    temp_c = temp_iface.GetValue()
                                    if temp_c is not None:
                                        self.generator_temp_fahrenheit = (temp_c * 9/5) + 32
                                        self.last_generator_temp_raw = self.generator_temp_fahrenheit
                                        logging.info(f"Initial generator temp: {self.generator_temp_fahrenheit:.1f}F")
                                        GLib.idle_add(self._trigger_derating)
                                except dbus.DBusException as e:
                                    logging.error(f"Failed to read initial temp: {e}")
                                
                                return True
                except dbus.DBusException as e:
                    # Expected for services without BusItem interface
                    if "UnknownObject" not in str(e) and "doesn't exist" not in str(e):
                        logging.debug(f"Error checking service {service}: {e}")
                    continue
                except Exception as e:
                    logging.debug(f"Unexpected error checking service {service}: {e}")
                    continue
                
                try:
                    obj = self.bus.get_object(service, PRODUCT_NAME_PATH)
                    name = dbus.Interface(obj, BUS_ITEM_INTERFACE).GetValue()
                    if name:
                        name_lower = name.lower()
                        for pattern in self.generator_temp_patterns:
                            if pattern in name_lower:
                                self.generator_temp_service = service
                                
                                self._register_items_changed_service(
                                    service,
                                    'generator_temp',
                                    self._on_generator_temp_value
                                )
                                
                                logging.info(f"Found generator temp sensor: {service} (matched pattern: {pattern})")
                                
                                try:
                                    temp_obj = self.bus.get_object(service, TEMPERATURE_PATH)
                                    temp_iface = dbus.Interface(temp_obj, BUS_ITEM_INTERFACE)
                                    temp_c = temp_iface.GetValue()
                                    if temp_c is not None:
                                        self.generator_temp_fahrenheit = (temp_c * 9/5) + 32
                                        self.last_generator_temp_raw = self.generator_temp_fahrenheit
                                        logging.info(f"Initial generator temp: {self.generator_temp_fahrenheit:.1f}F")
                                        GLib.idle_add(self._trigger_derating)
                                except dbus.DBusException as e:
                                    logging.error(f"Failed to read initial temp: {e}")
                                
                                return True
                except dbus.DBusException as e:
                    # Expected for services without BusItem interface
                    if "UnknownObject" not in str(e) and "doesn't exist" not in str(e):
                        logging.debug(f"Error checking service {service}: {e}")
                    continue
                except Exception as e:
                    logging.debug(f"Unexpected error checking service {service}: {e}")
                    continue
        return False
    
    def _find_gps_service(self):
        """Find GPS service for altitude"""
        services = [name for name in self.bus.list_names() if name.startswith(GPS_SERVICE_BASE)]
        if services:
            self.gps_service = services[0]
            
            self._register_items_changed_service(
                self.gps_service,
                'gps',
                self._on_altitude_value
            )
            
            logging.info(f"Found GPS: {self.gps_service}")
            
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
                            self.last_altitude_feet_raw = self.altitude_feet
                            logging.info(f"Initial altitude: {self.altitude_feet:.0f}ft")
                            GLib.idle_add(self._trigger_derating)
                    except (ValueError, TypeError, IndexError) as e:
                        logging.debug(f"Error parsing altitude value: {e}")
            except dbus.DBusException as e:
                logging.debug(f"Could not read initial altitude: {e}")
            
            return True
        return False
    
    def _should_trigger_derating(self, sensor_name, old_raw_value, new_raw_value, threshold=None):

        if threshold is None:
            threshold = getattr(self, 'SENSOR_CHANGE_THRESHOLD', 0.5)
        """Determine if sensor change should trigger derating recalculation"""
        if old_raw_value is None:
            return True
        
        change = abs(new_raw_value - old_raw_value)
        
        if sensor_name == 'altitude':
            return change >= self.ALTITUDE_THRESHOLD_FEET
        
        return change >= threshold
    
    def _on_transfer_switch_value(self, path, value):
        """Handle transfer switch value changes"""
        if path != STATE_PATH:
            return
        
        if value is None:
            logging.warning("Received None value for transfer switch state")
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
        
        if value is None:
            logging.warning("Received None value for Gen Auto Current state")
            return
        
        try:
            new_state = int(value)
        except (ValueError, TypeError):
            logging.error(f"Invalid Gen Auto Current value: {value}")
            return
        
        old_state = self.gen_auto_current_state
        self.gen_auto_current_state = new_state
        
        logging.info(f"Gen Auto Current: {'ON' if new_state == GEN_AUTO_CURRENT_ON else 'OFF'}")
        
        if new_state == GEN_AUTO_CURRENT_ON:
            logging.debug("Gen Auto Current enabled - forcing derating")
            GLib.idle_add(self._force_derating)
        else:
            logging.debug("Gen Auto Current disabled - reverting to saved limit")
            GLib.idle_add(self._revert_to_saved_limit)
    
    def _on_outdoor_temp_value(self, path, value):
        """Handle outdoor temperature value changes"""
        
        # Only process Temperature path
        if path != TEMPERATURE_PATH:
            logging.debug(f"Ignoring non-Temperature path for outdoor sensor: {path}")
            return
        
        if value is None:
            logging.warning("Received None value for outdoor temperature")
            return
        
        try:
            temp_c = float(value)
        except (ValueError, TypeError):
            logging.error(f"Invalid outdoor temperature value: {value}")
            return
        
        temp_f = (temp_c * 9/5) + 32
        old_raw = self.last_outdoor_temp_raw
        
        # Calculate precise change
        change = temp_f - self.outdoor_temp_fahrenheit
        
        # Always log at DEBUG level for troubleshooting
        logging.debug(f"Outdoor temp sensor update: {self.outdoor_temp_fahrenheit:.2f}F -> {temp_f:.2f}F (change: {change:+.2f}F)")
        
        if self._should_trigger_derating('outdoor_temp', old_raw, temp_f):
            old_temp = self.outdoor_temp_fahrenheit
            self.outdoor_temp_fahrenheit = temp_f
            self.last_outdoor_temp_raw = temp_f
            
            if self.gen_auto_current_state == GEN_AUTO_CURRENT_ON and self.startup_sync_complete:
                logging.debug(f"Outdoor temp changed significantly: {old_temp:.2f}F -> {temp_f:.2f}F (change: {temp_f - old_temp:+.2f}F) - triggering derating")
                GLib.idle_add(self._trigger_derating)
            elif self.gen_auto_current_state == GEN_AUTO_CURRENT_ON:
                logging.debug(f"Outdoor temp changed significantly: {old_temp:.2f}F -> {temp_f:.2f}F - will trigger derating after startup")
        else:
            # Update value but log that it didn't trigger derating
            self.outdoor_temp_fahrenheit = temp_f
            logging.debug(f"Outdoor temp change below threshold ({abs(temp_f - old_raw):.3f}F < {self.SENSOR_CHANGE_THRESHOLD}F) - no derating triggered")
    
    def _on_generator_temp_value(self, path, value):
        """Handle generator temperature value changes"""
        
        # Only process Temperature path
        if path != TEMPERATURE_PATH:
            logging.debug(f"Ignoring non-Temperature path for generator sensor: {path}")
            return
        
        if value is None:
            logging.warning("Received None value for generator temperature")
            return
        
        try:
            # Handle both direct values and nested structures
            if isinstance(value, dict) and 'Value' in value:
                temp_raw = value['Value']
            else:
                temp_raw = value
            
            # Temperature in Celsius from the sensor
            temp_c = float(temp_raw)
            
            # Convert to Fahrenheit
            temp_f = (temp_c * 9/5) + 32
            
        except (ValueError, TypeError) as e:
            logging.error(f"Invalid generator temperature value: {value}, error: {e}")
            return
        
        old_raw = self.last_generator_temp_raw
        
        # Calculate precise change
        change = temp_f - self.generator_temp_fahrenheit
        
        # Always log at DEBUG level for troubleshooting
        logging.debug(f"Generator temp sensor update: {self.generator_temp_fahrenheit:.2f}F -> {temp_f:.2f}F (change: {change:+.2f}F)")
        
        if self._should_trigger_derating('generator_temp', old_raw, temp_f):
            old_temp = self.generator_temp_fahrenheit
            self.generator_temp_fahrenheit = temp_f
            self.last_generator_temp_raw = temp_f
            
            if self.gen_auto_current_state == GEN_AUTO_CURRENT_ON and self.startup_sync_complete:
                logging.debug(f"Generator temp changed significantly: {old_temp:.1f}F -> {temp_f:.1f}F (change: {temp_f - old_temp:+.1f}F) - triggering derating")
                GLib.idle_add(self._trigger_derating)
            elif self.gen_auto_current_state == GEN_AUTO_CURRENT_ON:
                logging.debug(f"Generator temp changed significantly: {old_temp:.2f}F -> {temp_f:.2f}F - will trigger derating after startup")
        else:
            # Update value but log that it didn't trigger derating
            self.generator_temp_fahrenheit = temp_f
            logging.debug(f"Generator temp change below threshold ({abs(temp_f - old_raw):.3f}F < {self.SENSOR_CHANGE_THRESHOLD}F) - no derating triggered")
    
    def _on_altitude_value(self, path, value):
        """Handle altitude value changes"""
        if path != ALTITUDE_PATH:
            return
        
        if value is None:
            logging.warning("Received None value for altitude")
            return
        
        try:
            if isinstance(value, dbus.Array):
                alt_m = float(value[0]) if value and value[0] is not None else None
            else:
                alt_m = float(value) if value is not None else None
            
            if alt_m is None:
                return
                
            new_altitude_ft = alt_m * 3.28084
            old_raw = self.last_altitude_feet_raw
            
            # Calculate precise change
            change = new_altitude_ft - self.altitude_feet
            
            # Always log at DEBUG level for troubleshooting
            logging.debug(f"Altitude sensor update: {self.altitude_feet:.1f}ft -> {new_altitude_ft:.1f}ft (change: {change:+.1f}ft)")
            
            if self._should_trigger_derating('altitude', old_raw, new_altitude_ft):
                old_alt = self.altitude_feet
                self.altitude_feet = new_altitude_ft
                self.last_altitude_feet_raw = new_altitude_ft
                
                if self.gen_auto_current_state == GEN_AUTO_CURRENT_ON and self.startup_sync_complete:
                    logging.debug(f"Altitude changed significantly: {old_alt:.1f}ft -> {self.altitude_feet:.1f}ft (change: {self.altitude_feet - old_alt:+.1f}ft) - triggering derating")
                    GLib.idle_add(self._trigger_derating)
                elif self.gen_auto_current_state == GEN_AUTO_CURRENT_ON:
                    logging.debug(f"Altitude changed significantly: {old_alt:.1f}ft -> {self.altitude_feet:.1f}ft - will trigger derating after startup")
            else:
                # Update value but log that it didn't trigger derating
                old_alt = self.altitude_feet
                self.altitude_feet = new_altitude_ft
                logging.debug(f"Altitude change below threshold ({abs(new_altitude_ft - old_raw):.1f}ft < {self.ALTITUDE_THRESHOLD_FEET}ft) - no derating triggered")
                
        except (ValueError, TypeError, IndexError) as e:
            logging.debug(f"Error processing altitude: {e}")
    
    def _on_active_limit_changed(self, *args, **kwargs):
        """Callback for active current limit changes"""
        if not self.startup_sync_complete:
            return
        
        if args and isinstance(args[0], dict):
            payload = args[0]
            if 'Value' in payload:
                new_limit = payload['Value']
                if new_limit is not None:
                    logging.debug(f"Active limit change: {new_limit}A")
                    self._handle_active_limit_change(float(new_limit))
    
    def _on_generator_limit_changed(self, *args, **kwargs):
        """Callback for generator current limit changes"""
        if not self.startup_sync_complete:
            return
        
        if args and isinstance(args[0], dict):
            payload = args[0]
            if 'Value' in payload:
                new_limit = payload['Value']
                if new_limit is not None:
                    logging.debug(f"Generator limit change: {new_limit}A")
                    self._handle_generator_limit_change(float(new_limit))
    
    def _on_grid_limit_changed(self, *args, **kwargs):
        """Callback for grid current limit changes"""
        if not self.startup_sync_complete:
            return
        
        if args and isinstance(args[0], dict):
            payload = args[0]
            if 'Value' in payload:
                new_limit = payload['Value']
                if new_limit is not None:
                    logging.debug(f"Grid limit change: {new_limit}A")
                    self._handle_grid_limit_change(float(new_limit))
    
    def _handle_active_limit_change(self, new_limit):
        """Handle active limit change - sync to saved settings"""
        if self.transfer_state != TransferState.IDLE:
            logging.debug(f"Active limit change ignored - transfer in progress")
            return
        
        try:
            current_input_type = self.ac_input_type_obj.GetValue() if self.ac_input_type_obj else None
        except Exception as e:
            logging.error(f"Failed to get input type: {e}")
            return
        
        if self.gen_auto_current_state == GEN_AUTO_CURRENT_ON and self._is_generator_running():
            logging.debug("Gen Auto ON - overriding external change with derated value")
            GLib.idle_add(lambda: self._perform_derating(AC_ACTIVE_INPUT_CURRENT_LIMIT_PATH, force=True))
            GLib.idle_add(lambda: self._perform_derating(GENERATOR_CURRENT_LIMIT_PATH, force=True))
            return
        
        if current_input_type == 2:
            if self.gen_auto_current_state != GEN_AUTO_CURRENT_ON:
                current_saved = self.DbusSettings['generatorCurrentLimit']
                if abs(new_limit - current_saved) > 0.1:
                    logging.debug(f"Syncing saved generator limit from {current_saved}A to {new_limit}A")
                    self.DbusSettings['generatorCurrentLimit'] = new_limit
                    self.last_derated_gen_setting = new_limit
        elif current_input_type in (1, 3):
            current_saved = self.DbusSettings['gridCurrentLimit']
            if abs(new_limit - current_saved) > 0.1:
                logging.debug(f"Syncing saved grid limit from {current_saved}A to {new_limit}A")
                self.DbusSettings['gridCurrentLimit'] = new_limit
    
    def _handle_generator_limit_change(self, new_limit):
        """Handle saved generator limit change - sync to active if on generator"""
        if self.transfer_state != TransferState.IDLE:
            return
        
        self.DbusSettings['generatorCurrentLimit'] = new_limit
        self.last_derated_gen_setting = new_limit
        
        if self.gen_auto_current_state == GEN_AUTO_CURRENT_ON:
            logging.debug("Gen Auto ON - overriding with derated value")
            GLib.idle_add(lambda: self._perform_derating(GENERATOR_CURRENT_LIMIT_PATH, force=True))
            if self._is_generator_running():
                GLib.idle_add(lambda: self._perform_derating(AC_ACTIVE_INPUT_CURRENT_LIMIT_PATH, force=True))
            return
        
        try:
            current_input_type = self.ac_input_type_obj.GetValue() if self.ac_input_type_obj else None
            if current_input_type == 2:
                if self.current_limit_is_adjustable_obj and self.current_limit_is_adjustable_obj.GetValue() == 1:
                    logging.debug(f"Applying generator limit {new_limit}A to active")
                    self.current_limit_obj.SetValue(wrap_dbus_value(new_limit))
                    self.last_derated_active_limit = new_limit
        except Exception as e:
            logging.error(f"Failed to apply generator limit to active: {e}")
    
    def _handle_grid_limit_change(self, new_limit):
        """Handle saved grid limit change - sync to active if on grid/shore"""
        if self.transfer_state != TransferState.IDLE:
            return
        
        self.DbusSettings['gridCurrentLimit'] = new_limit
        
        try:
            current_input_type = self.ac_input_type_obj.GetValue() if self.ac_input_type_obj else None
            if current_input_type in (1, 3):
                if self.current_limit_is_adjustable_obj and self.current_limit_is_adjustable_obj.GetValue() == 1:
                    logging.debug(f"Applying grid limit {new_limit}A to active")
                    self.current_limit_obj.SetValue(wrap_dbus_value(new_limit))
                    self.last_derated_active_limit = new_limit
        except Exception as e:
            logging.error(f"Failed to apply grid limit to active: {e}")
    
    def _is_generator_running(self):
        """Check if generator is currently running"""
        if self.transfer_switch_service:
            try:
                obj = self.bus.get_object(self.transfer_switch_service, STATE_PATH)
                iface = dbus.Interface(obj, BUS_ITEM_INTERFACE)
                state = iface.GetValue()
                return state in GENERATOR_ON_VALUE
            except dbus.DBusException as e:
                logging.debug(f"Could not check generator state: {e}")
                return False
            except Exception as e:
                logging.debug(f"Unexpected error checking generator state: {e}")
                return False
        return False
    
    def _trigger_derating(self):
        """Trigger derating calculation with debounce"""
        if not self.startup_sync_complete:
            return
        
        if self.transfer_state != TransferState.IDLE:
            return
        
        # Debounce derating to prevent multiple rapid triggers
        if hasattr(self, '_derating_pending') and self._derating_pending:
            logging.debug("Derating already pending, skipping")
            return
        
        self._derating_pending = True
        
        def execute_derating():
            self._derating_pending = False
            if self.gen_auto_current_state == GEN_AUTO_CURRENT_ON:
                if self._is_generator_running():
                    self._perform_derating(AC_ACTIVE_INPUT_CURRENT_LIMIT_PATH, force=False)
                    self._perform_derating(GENERATOR_CURRENT_LIMIT_PATH, force=False)
                else:
                    self._perform_derating(GENERATOR_CURRENT_LIMIT_PATH, force=False)
        
        # Schedule with a short delay to allow multiple sensor updates to settle
        GLib.timeout_add(100, execute_derating)
    
    def _force_derating(self):
        """Force derating update"""
        if not self.startup_sync_complete:
            return
        
        if self.transfer_state != TransferState.IDLE:
            GLib.timeout_add_seconds(1, self._force_derating)
            return
        
        logging.debug("Forcing derating update")
        
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
        derated = derated * altitude_multiplier
        derated = derated * temperature_multiplier
        derated = derated * generator_temp_multiplier
        derated = derated * self.OUTPUT_BUFFER
        
        return round(derated, 1)
    
    def _perform_derating(self, target_path, force=False):
        """Calculate and apply derated value"""
        if not self.startup_sync_complete:
            return
        
        if self.transfer_state != TransferState.IDLE:
            return
        
        # Prevent rapid duplicate derates (debounce)
        current_time = time.time()
        if hasattr(self, '_last_derate_time'):
            if current_time - self._last_derate_time < 0.5:  # 500ms debounce
                logging.debug(f"Skipping derate - too soon since last derate ({current_time - self._last_derate_time:.3f}s ago)")
                return
        self._last_derate_time = current_time
        
        try:
            derated = self.calculate_derating_factor(
                self.outdoor_temp_fahrenheit, self.altitude_feet, self.generator_temp_fahrenheit
            )
            
            should_update = force
            if not should_update:
                if target_path == GENERATOR_CURRENT_LIMIT_PATH:
                    if self.last_derated_gen_setting is None or abs(derated - self.last_derated_gen_setting) > 0.05:
                        should_update = True
                else:
                    if self.last_derated_active_limit is None or abs(derated - self.last_derated_active_limit) > 0.05:
                        should_update = True
            
            if not should_update:
                logging.debug(f"Derate not needed - {target_path} already at {derated}A")
                return
            
            if target_path == GENERATOR_CURRENT_LIMIT_PATH:
                service = SETTINGS_SERVICE_NAME
                desc = "Generator Limit"
            else:
                service = self.vebus_service
                desc = "Active Limit"
            
            current, _ = self._get_dbus_value(service, target_path)
            
            if current is None or abs(float(current) - derated) > 0.05 or force:
                self._set_dbus_value(service, target_path, derated)
                logging.debug(f"Derated {desc} to {derated}A (temp: {self.outdoor_temp_fahrenheit:.1f}F, alt: {self.altitude_feet:.0f}ft, gen_temp: {self.generator_temp_fahrenheit:.1f}F)")
                
                if target_path == GENERATOR_CURRENT_LIMIT_PATH:
                    self.last_derated_gen_setting = derated
                else:
                    self.last_derated_active_limit = derated
                    
        except Exception as e:
            logging.error(f"Derating failed: {e}")
    
    def _monitor_lock_health(self):
        """Periodic health check for the transfer lock"""
        if self.transfer_lock.is_locked:
            holder = self.transfer_lock.get_holder()
            duration = self.transfer_lock.get_hold_duration()
            watchdog_timeout = self.transfer_lock.watchdog_timeout
            
            warning_threshold = watchdog_timeout * 0.8
            if duration > warning_threshold:
                logging.warning(f"Lock held by '{holder}' for {duration:.1f}s (watchdog: {watchdog_timeout}s)")
                
                if self.transfer_state == TransferState.IDLE:
                    logging.error(f"Lock held in IDLE state by '{holder}' - forcing release")
                    self.transfer_lock.force_release("idle_state_stuck")
                elif self.transfer_state == TransferState.WAITING_FOR_GENERATOR_SHUTDOWN:
                    remaining = self.SHUTDOWN_TIMER_SECONDS - (duration - 30)
                    if remaining > 0:
                        logging.debug(f"Lock held during generator shutdown - {remaining:.0f}s remaining")
                    else:
                        logging.warning(f"Generator shutdown timer appears stuck - {duration:.1f}s elapsed")
                elif duration > watchdog_timeout + 10:
                    logging.error(f"Lock held for {duration:.1f}s during {self.transfer_state} - forcing release")
                    self.transfer_lock.force_release("extended_hold")
        
        return True
    
    def _periodic_status(self):
        """Periodic status report - reduced frequency (every 5 minutes)"""
        if self.startup_sync_complete:
            current_active = None
            try:
                if self.current_limit_obj:
                    current_active = self.current_limit_obj.GetValue()
            except Exception as e:
                logging.debug(f"Could not read active limit for status: {e}")
            
            lock_holder = self.transfer_lock.get_holder()
            lock_duration = self.transfer_lock.get_hold_duration()
            lock_timeout = self.transfer_lock.watchdog_timeout
            
            if not self.transfer_lock.is_locked:
                lock_status = "FREE"
            else:
                lock_status = f"HELD by {lock_holder} for {lock_duration:.1f}s"
            
            # Keep this at INFO for regular monitoring
            logging.info(f"STATUS - Lock: {lock_status}, Gen Auto: {self.gen_auto_current_state} ({'ON' if self.gen_auto_current_state == GEN_AUTO_CURRENT_ON else 'OFF'}), "
                         f"State: {self.transfer_state.value}, Active Limit: {current_active}A, "
                         f"Gen Running: {self._is_generator_running()}, "
                         f"Sensors: Outdoor={self.outdoor_temp_fahrenheit:.1f}F, GenTemp={self.generator_temp_fahrenheit:.1f}F, Alt={self.altitude_feet:.0f}ft")
        else:
            logging.warning("Startup sync not complete - waiting for services")
        return True
    
    def _get_dbus_value(self, service_name, path):
        """Get D-Bus value"""
        if not service_name:
            return None, False
        try:
            obj = self.bus.get_object(service_name, path)
            interface = dbus.Interface(obj, BUS_ITEM_INTERFACE)
            return interface.GetValue(), False
        except dbus.DBusException as e:
            logging.debug(f"D-Bus error getting {path}: {e}")
            return None, False
        except Exception as e:
            logging.debug(f"Unexpected error getting {path}: {e}")
            return None, False
    
    def _set_dbus_value(self, service_name, path, value):
        """Set D-Bus value"""
        if not service_name:
            return
        try:
            obj = self.bus.get_object(service_name, path)
            interface = dbus.Interface(obj, BUS_ITEM_INTERFACE)
            interface.SetValue(wrap_dbus_value(value))
        except dbus.DBusException as e:
            logging.error(f"D-Bus error setting {path}: {e}")
        except Exception as e:
            logging.error(f"Unexpected error setting {path}: {e}")
    
    def _transfer_to_generator(self):
        """Transfer to generator"""
        try:
            self.transfer_state = TransferState.TRANSFERRING_TO_GENERATOR
            logging.info("Transferring to GENERATOR")
            
            target_limit = self.DbusSettings['generatorCurrentLimit']
            
            self.ac_input_type_obj.SetValue(wrap_dbus_value(2))
            
            if self.current_limit_is_adjustable_obj and self.current_limit_is_adjustable_obj.GetValue() == 1:
                self.current_limit_obj.SetValue(wrap_dbus_value(target_limit))
                self.last_derated_active_limit = target_limit
            
            logging.info("Generator transfer complete")
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
        """Execute grid transfer after delay - non-blocking implementation"""
        try:
            self.transfer_state = TransferState.TRANSFERRING_TO_GRID
            logging.info("Transferring to GRID")
            
            # Non-blocking disable of IgnoreAcIn1 if needed (no sleep required)
            try:
                if self.ignore_ac_in_1_obj:
                    current = self.ignore_ac_in_1_obj.GetValue()
                    if current == 1:
                        logging.info("Disabling IgnoreAcIn1")
                        self.ignore_ac_in_1_obj.SetValue(wrap_dbus_value(0))
                        # D-Bus SetValue is synchronous - no sleep needed
            except dbus.DBusException as e:
                logging.debug(f"Could not check/disable IgnoreAcIn1: {e}")
            except Exception as e:
                logging.debug(f"Unexpected error with IgnoreAcIn1: {e}")
            
            target_type = self.DbusSettings['gridInputType']
            target_limit = self.DbusSettings['gridCurrentLimit']
            
            self.ac_input_type_obj.SetValue(wrap_dbus_value(target_type))
            
            if self.current_limit_is_adjustable_obj and self.current_limit_is_adjustable_obj.GetValue() == 1:
                self.current_limit_obj.SetValue(wrap_dbus_value(target_limit))
                self.last_derated_active_limit = target_limit
            
            logging.info("Grid transfer complete")
            
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
            except dbus.DBusException as e:
                logging.error(f"Could not set RemoteGeneratorSelected: {e}")
            except Exception as e:
                logging.error(f"Unexpected error setting RemoteGeneratorSelected: {e}")
    
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
    
    # Default to INFO, can be overridden with environment variable
    log_level = os.environ.get('GEN_AUTO_LOG_LEVEL', 'INFO')
    logger.setLevel(getattr(logging, log_level))
    
    logging.info(f"Log level set to {log_level}")

def main():
    setup_logging()
    
    logging.info("=" * 60)
    logging.info("External Transfer Switch Monitor With Auto Gen Current starting")
    logging.info("=" * 60)
    
    DynamicTransferSwitch()
    
    GLib.MainLoop().run()

if __name__ == "__main__":
    main()
