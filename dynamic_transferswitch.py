#!/usr/bin/env python3

"""
Dynamic Transfer Switch with Generator Auto Current Derating

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

from gi.repository import GLib

sys.path.insert(
    1,
    "/opt/victronenergy/dbus-systemcalc-py/ext/velib_python"
)

from vedbus import VeDbusService
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
TEMPERATURE_PATH = "/Temperature"
CUSTOM_NAME_PATH = "/CustomName"
STATE_PATH = "/State"
PRODUCT_NAME_PATH = "/ProductName"
BUS_ITEM_INTERFACE = "com.victronenergy.BusItem"
GENERATOR_CURRENT_LIMIT_PATH = "/Settings/TransferSwitch/GeneratorCurrentLimit"

# Transfer switch state values
GENERATOR_ON_VALUE = (12, 3)
SHORE_POWER_ON_VALUE = (13, 2)

# Gen Auto Current State Values
GEN_AUTO_CURRENT_OFF = 2
GEN_AUTO_CURRENT_ON = 3

# Configuration file path
CONFIG_FILE_PATH = '/data/apps/dynamic_transferswitch/config.ini'

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
        self.startup_settle_done = False
        
        # D-Bus objects
        self.vebus_service = None
        self.acInputTypeObj = None
        self.numberOfAcInputs = 0
        self.currentLimitObj = None
        self.currentLimitIsAdjustableObj = None
        self.ignoreAcIn1Obj = None
        self.remoteGeneratorSelectedItem = None
        self.remoteGeneratorSelectedLocalValue = -1
        self.transferSwitchStateObj = None
        self.transferSwitchNameObj = None
        
        # Sensor services
        self.outdoor_temp_service_name = None
        self.generator_temp_service_name = None
        self.gps_service_name = None
        self.transfer_switch_service = None
        self.gen_auto_current_service = None
        
        # Sensor values
        self.outdoor_temp_fahrenheit = self.DEFAULT_OUTDOOR_TEMP_F
        self.altitude_feet = self.DEFAULT_ALTITUDE_FEET
        self.generator_temp_fahrenheit = self.DEFAULT_GENERATOR_TEMP_F
        self.gen_auto_current_state = None
        self.previous_gen_auto_current_state = None
        
        # Error logging flags
        self.altitude_warning_logged = False
        self.generator_temp_warning_logged = False
        self.outdoor_temp_warning_logged = False
        self.altitude_dbus_error_logged = False
        
        # Debouncing
        self.debounce_timer = None
        self.pending_generator_state = None
        
        # Service discovery
        self.tsInputSearchDelay = 10
        self.firstSearchDone = False
        self.veBusFoundInitially = False
        self.loggedVeBusInitialNotFound = False
        self.dbusOk = False
        self.transferSwitchActive = False
        self.transferSwitchLocation = 0
        self.initial_derated_output_logged = False
        
        # Track last derated value to avoid unnecessary writes
        self.last_derated_active_limit = None
        self.last_derated_gen_setting = None
        
        # D-Bus settings
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
            eventCallback=self.settings_changed
        )
        
        if not self.validate_settings():
            logging.error("Initial settings validation failed")

        if self.DbusSettings['gridInputType'] == 2:
            logging.warning("grid input type was generator - resetting to grid")
            self.DbusSettings['gridInputType'] = 1
        
        # Start startup sequence (runs once)
        GLib.idle_add(self._startup_sequence)
        GLib.timeout_add_seconds(1, self.background)
        
        self.last_validation = time.time()
        
    def _load_and_set_config(self):
        config = configparser.ConfigParser()
        
        # Defaults
        self.BASE_TEMPERATURE_THRESHOLD_F = 77.0
        self.TEMP_COEFFICIENT = 0.006
        self.ALTITUDE_COEFFICIENT = 0.00003
        self.BASE_GENERATOR_OUTPUT_AMPS = 62.5
        self.OUTPUT_BUFFER = 0.9
        self.HIGH_GENTEMP_THRESHOLD_F = 220.0
        self.MEDIUM_GENTEMP_THRESHOLD_F = 212.0
        self.HIGH_GENTEMP_REDUCTION = 0.85
        self.MEDIUM_GENTEMP_REDUCTION = 0.90
        self.DEFAULT_ALTITUDE_FEET = 1000.0
        self.DEFAULT_GENERATOR_TEMP_F = 180.0
        self.DEFAULT_OUTDOOR_TEMP_F = 77.0
        self.SHUTDOWN_TIMER_SECONDS = 5
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
    
    def _get_transfer_switch_state_direct(self):
        """Directly read transfer switch state without updating internal state"""
        if self.transferSwitchActive and self.transferSwitchStateObj:
            try:
                state = self.transferSwitchStateObj.GetValue()
                if state in (12, 3):
                    return True  # Generator
                elif state in (13, 2):
                    return False  # Grid/Shore
            except Exception as e:
                logging.debug(f"Error reading transfer switch state: {e}")
        return None
    
    def _startup_sequence(self):
        """Run startup sequence exactly once"""
        if self.startup_sequence_run or self.startup_sync_complete:
            return False
        
        self.startup_sequence_run = True
        logging.info("=" * 60)
        logging.info("STARTUP SEQUENCE - Discovering services")
        logging.info("=" * 60)
        
        # Discover services with retries
        for attempt in range(10):
            logging.info(f"Discovery attempt {attempt + 1}/10")
            
            self._find_vebus_service()
            self._find_transfer_switch_input_internal()
            self._find_outdoor_temperature_service()
            self._find_generator_temperature_service()
            self._find_gps_service_internal()
            self._find_gen_auto_current_input_internal()
            
            if self.vebus_service and self.transfer_switch_service:
                logging.info("Required services found")
                break
            else:
                missing = []
                if not self.vebus_service:
                    missing.append("VE.Bus")
                if not self.transfer_switch_service:
                    missing.append("Transfer Switch")
                logging.warning(f"Missing: {', '.join(missing)}")
                if attempt < 9:
                    time.sleep(1)
        
        if not self.vebus_service or not self.transfer_switch_service:
            logging.error("Required services not found - startup aborted")
            self.startup_sync_complete = True
            return False
        
        # Acquire lock for startup synchronization
        lock_acquired = self.transfer_lock.acquire("startup", timeout=5)
        if not lock_acquired:
            logging.error("Could not acquire lock for startup")
            self.startup_sync_complete = True
            return False
        
        try:
            # Synchronize state
            logging.info("=" * 60)
            logging.info("STARTUP SYNCHRONIZATION")
            logging.info("=" * 60)
            
            # Wait for transfer switch state to stabilize
            logging.info("Waiting for transfer switch state to stabilize...")
            time.sleep(1)
            
            # Read transfer switch state multiple times directly to ensure stability
            stable_count = 0
            last_state = None
            for i in range(5):
                current_state = self._get_transfer_switch_state_direct()
                if current_state is not None:
                    if current_state == last_state:
                        stable_count += 1
                    else:
                        stable_count = 0
                        last_state = current_state
                    logging.debug(f"State read {i+1}: {'GENERATOR' if current_state else 'GRID/SHORE'}")
                time.sleep(0.2)
            
            if stable_count < 3:
                logging.warning(f"Transfer switch state unstable, using last known state: {last_state}")
            
            transfer_switch_state = last_state if last_state is not None else False
            
            # Also update the internal onGenerator state
            self.onGenerator = transfer_switch_state
            
            # Read current AC state
            try:
                current_input_type = self.acInputTypeObj.GetValue()
                current_limit = self.currentLimitObj.GetValue() if self.currentLimitObj else None
                logging.info(f"Current AC Input: {current_input_type} (1=Grid,2=Gen,3=Shore)")
                logging.info(f"Current Limit: {current_limit}A")
            except Exception as e:
                logging.error(f"Failed to read AC state: {e}")
                return False
            
            saved_grid_limit = self.DbusSettings['gridCurrentLimit']
            saved_gen_limit = self.DbusSettings['generatorCurrentLimit']
            saved_grid_type = self.DbusSettings['gridInputType']
            
            logging.info(f"Transfer Switch (stable): {'GENERATOR' if transfer_switch_state else 'GRID/SHORE'}")
            logging.info(f"Saved Grid Limit: {saved_grid_limit}A")
            logging.info(f"Saved Generator Limit: {saved_gen_limit}A")
            
            # Apply correct settings if needed
            if transfer_switch_state:
                # Should be on generator
                if current_input_type != 2:
                    logging.info("Applying generator settings...")
                    try:
                        self.acInputTypeObj.SetValue(wrap_dbus_value(2))
                        if self.currentLimitIsAdjustableObj and self.currentLimitIsAdjustableObj.GetValue() == 1:
                            self.currentLimitObj.SetValue(wrap_dbus_value(saved_gen_limit))
                        time.sleep(1)
                        logging.info("Generator settings applied during startup")
                    except Exception as e:
                        logging.error(f"Failed to apply generator settings: {e}")
                else:
                    logging.info("Already on GENERATOR")
                    # Update saved limit from active if different
                    if current_limit is not None and abs(current_limit - saved_gen_limit) > 0.5:
                        logging.info(f"Updating saved generator limit from {saved_gen_limit}A to {current_limit}A")
                        self.DbusSettings['generatorCurrentLimit'] = current_limit
                
                # Set initial state for monitoring
                self.onGenerator = True
                self.lastOnGenerator = True
            else:
                # Should be on grid/shore
                if current_input_type != saved_grid_type:
                    logging.info("Applying grid/shore settings...")
                    try:
                        self.acInputTypeObj.SetValue(wrap_dbus_value(saved_grid_type))
                        if self.currentLimitIsAdjustableObj and self.currentLimitIsAdjustableObj.GetValue() == 1:
                            self.currentLimitObj.SetValue(wrap_dbus_value(saved_grid_limit))
                        time.sleep(1)
                        logging.info("Grid/Shore settings applied during startup")
                    except Exception as e:
                        logging.error(f"Failed to apply grid settings: {e}")
                else:
                    logging.info("Already on GRID/SHORE")
                    # Update saved limit from active if different
                    if current_limit is not None and abs(current_limit - saved_grid_limit) > 0.5:
                        logging.info(f"Updating saved grid limit from {saved_grid_limit}A to {current_limit}A")
                        self.DbusSettings['gridCurrentLimit'] = current_limit
                
                # Set initial state for monitoring
                self.onGenerator = False
                self.lastOnGenerator = False
            
            # Read initial sensor values
            self._read_initial_values()
            
            self.startup_sync_complete = True
            logging.info("=" * 60)
            logging.info("STARTUP COMPLETE - Normal operations")
            logging.info("=" * 60)
            
            return False
            
        except Exception as e:
            logging.error(f"Startup synchronization failed: {e}")
            return False
        finally:
            # ALWAYS release the startup lock
            self.transfer_lock.release("startup")
    
    def _read_initial_values(self):
        self._update_outdoor_temperature(log_update=False, log_initial=True)
        self._update_altitude(log_update=False, log_initial=True)
        self._update_generator_temperature(log_update=False, log_initial=True)
        self._update_gen_auto_current_state(initial_read=True)
    
    def _find_service(self, service_base):
        services = [name for name in self.bus.list_names() if name.startswith(service_base)]
        return services[0] if services else None
    
    def _find_vebus_service(self):
        self.vebus_service = self._find_service(VEBUS_SERVICE_BASE)
        if self.vebus_service:
            self._setup_vebus_objects()
    
    def _setup_vebus_objects(self):
        try:
            self.numberOfAcInputs = self.bus.get_object(self.vebus_service, "/Ac/NumberOfAcInputs").GetValue()
            self.currentLimitObj = self.bus.get_object(self.vebus_service, "/Ac/ActiveIn/CurrentLimit")
            self.currentLimitIsAdjustableObj = self.bus.get_object(self.vebus_service, "/Ac/ActiveIn/CurrentLimitIsAdjustable")
            self.ignoreAcIn1Obj = self.bus.get_object(self.vebus_service, "/Ac/Control/IgnoreAcIn1")
            
            # Setup signal monitoring for active current limit
            try:
                self.currentLimitObj.connect_to_signal("PropertiesChanged", self._active_limit_changed)
                logging.info("Monitoring active current limit for changes")
            except Exception as e:
                logging.debug(f"Could not monitor active limit: {e}")
            
            try:
                self.remoteGeneratorSelectedItem = self.bus.get_object(self.vebus_service, "/Ac/Control/RemoteGeneratorSelected")
            except:
                self.remoteGeneratorSelectedItem = None
            
            logging.info(f"Discovered { 'Quattro' if self.numberOfAcInputs == 2 else 'MultiPlus' } at {self.vebus_service}")
            self._setup_ac_input_objects()
            self.dbusOk = True
        except Exception as e:
            logging.error(f"Failed to setup VE.Bus: {e}")
            self.dbusOk = False
    
    def _active_limit_changed(self, *args):
        """Called when active current limit changes externally"""
        if not self.startup_sync_complete:
            return
        
        # Skip if a transfer is in progress
        if self.transfer_state != TransferState.IDLE:
            return
        
        # If Gen Auto Current is ON and generator is running, override any external change
        if self.gen_auto_current_state == GEN_AUTO_CURRENT_ON and self._is_generator_running():
            logging.info("Active current limit changed externally while Gen Auto ON - overriding with derated value")
            GLib.idle_add(lambda: self._perform_derating(AC_ACTIVE_INPUT_CURRENT_LIMIT_PATH, force=True))
            # Also ensure saved generator limit is correct
            GLib.idle_add(lambda: self._perform_derating(GENERATOR_CURRENT_LIMIT_PATH, force=True))
    
    def _setup_ac_input_objects(self):
        if self.numberOfAcInputs == 0:
            loc = 0
        elif self.numberOfAcInputs == 1:
            loc = 1
        elif self.DbusSettings.get('transferSwitchOnAc2', 0) == 1:
            loc = 2
        else:
            loc = 1
        
        self.transferSwitchLocation = loc
        
        try:
            if loc == 2:
                self.acInputTypeObj = self.bus.get_object(SETTINGS_SERVICE_NAME, "/Settings/SystemSetup/AcInput2")
            else:
                self.acInputTypeObj = self.bus.get_object(SETTINGS_SERVICE_NAME, "/Settings/SystemSetup/AcInput1")
        except Exception as e:
            logging.error(f"AC input setup failed: {e}")
    
    def _get_dbus_value(self, service_name, path):
        if not service_name:
            return None, False
        try:
            obj = self.bus.get_object(service_name, path)
            interface = dbus.Interface(obj, BUS_ITEM_INTERFACE)
            return interface.GetValue(), False
        except dbus.exceptions.DBusException as e:
            is_service_unknown = "DBus.Error.ServiceUnknown" in str(e)
            return None, is_service_unknown
        except Exception as e:
            logging.error(f"Error getting {path}: {e}")
            return None, False
    
    def _set_dbus_value(self, service_name, path, value):
        if not service_name:
            return
        try:
            obj = self.bus.get_object(service_name, path)
            interface = dbus.Interface(obj, BUS_ITEM_INTERFACE)
            interface.SetValue(wrap_dbus_value(value))
            logging.debug(f"Set {path} to {value}")
        except Exception as e:
            logging.error(f"Failed to set {path}: {e}")
    
    def _find_outdoor_temperature_service(self):
        """Find temperature sensor with 'outdoor' in custom name (case-insensitive)"""
        self.outdoor_temp_service_name = None
        for service in self.bus.list_names():
            if service.startswith(TEMPERATURE_SERVICE_BASE):
                try:
                    obj = self.bus.get_object(service, CUSTOM_NAME_PATH)
                    name = dbus.Interface(obj, BUS_ITEM_INTERFACE).GetValue()
                    if name and "outdoor" in name.lower():
                        self.outdoor_temp_service_name = service
                        logging.info(f"Found outdoor temperature service at {service} with name '{name}'")
                        return
                except:
                    pass
    
    def _find_generator_temperature_service(self):
        """Find temperature sensor for generator with multiple patterns (case-insensitive)"""
        self.generator_temp_service_name = None
        search_patterns = ["gen", "generator", "gen temp", "generator temp"]
        
        for service in self.bus.list_names():
            if service.startswith(TEMPERATURE_SERVICE_BASE):
                # Check CustomName
                try:
                    obj = self.bus.get_object(service, CUSTOM_NAME_PATH)
                    name = dbus.Interface(obj, BUS_ITEM_INTERFACE).GetValue()
                    if name:
                        name_lower = name.lower()
                        for pattern in search_patterns:
                            if pattern in name_lower:
                                self.generator_temp_service_name = service
                                logging.info(f"Found generator temperature service at {service} with CustomName '{name}'")
                                return
                except:
                    pass
                
                # Check ProductName
                try:
                    obj = self.bus.get_object(service, PRODUCT_NAME_PATH)
                    name = dbus.Interface(obj, BUS_ITEM_INTERFACE).GetValue()
                    if name:
                        name_lower = name.lower()
                        for pattern in search_patterns:
                            if pattern in name_lower:
                                self.generator_temp_service_name = service
                                logging.info(f"Found generator temperature service at {service} with ProductName '{name}'")
                                return
                except:
                    pass
    
    def _find_gps_service_internal(self):
        self.gps_service_name = self._find_service(GPS_SERVICE_BASE)
        if self.gps_service_name:
            logging.info(f"Found GPS service at {self.gps_service_name}")
    
    def _find_transfer_switch_input_internal(self):
        """Find digital input configured as transfer switch (case-insensitive)"""
        self.transfer_switch_service = None
        for service in self.bus.list_names():
            if service.startswith(DIGITAL_INPUT_SERVICE_BASE):
                try:
                    obj = self.bus.get_object(service, PRODUCT_NAME_PATH)
                    name = dbus.Interface(obj, BUS_ITEM_INTERFACE).GetValue()
                    if name and "transfer switch" in name.lower():
                        self.transfer_switch_service = service
                        self.transferSwitchNameObj = self.bus.get_object(service, '/CustomName')
                        self.transferSwitchStateObj = self.bus.get_object(service, '/State')
                        self.transferSwitchActive = True
                        logging.info(f"Found transfer switch at {service} with product name '{name}'")
                        return
                except:
                    pass
    
    def _find_gen_auto_current_input_internal(self):
        """Find digital input for Gen Auto Current enable/disable (case-insensitive)"""
        self.gen_auto_current_service = None
        for service in self.bus.list_names():
            if service.startswith(DIGITAL_INPUT_SERVICE_BASE):
                try:
                    obj = self.bus.get_object(service, PRODUCT_NAME_PATH)
                    name = dbus.Interface(obj, BUS_ITEM_INTERFACE).GetValue()
                    if name and "gen auto current" in name.lower():
                        self.gen_auto_current_service = service
                        logging.info(f"Found Gen Auto Current at {service} with product name '{name}'")
                        return
                except:
                    pass
    
    def _check_service_health(self):
        """Check if discovered services are still responding"""
        # Check outdoor temperature service
        if self.outdoor_temp_service_name:
            try:
                self.bus.get_object(self.outdoor_temp_service_name, TEMPERATURE_PATH)
            except:
                logging.warning(f"Outdoor temperature service {self.outdoor_temp_service_name} no longer available")
                self.outdoor_temp_service_name = None
        
        # Check generator temperature service
        if self.generator_temp_service_name:
            try:
                self.bus.get_object(self.generator_temp_service_name, TEMPERATURE_PATH)
            except:
                logging.warning(f"Generator temperature service {self.generator_temp_service_name} no longer available")
                self.generator_temp_service_name = None
        
        # Check GPS service
        if self.gps_service_name:
            try:
                self.bus.get_object(self.gps_service_name, ALTITUDE_PATH)
            except:
                logging.warning(f"GPS service {self.gps_service_name} no longer available")
                self.gps_service_name = None
        
        # Check Gen Auto Current service
        if self.gen_auto_current_service:
            try:
                self.bus.get_object(self.gen_auto_current_service, STATE_PATH)
            except:
                logging.warning(f"Gen Auto Current service {self.gen_auto_current_service} no longer available")
                self.gen_auto_current_service = None
    
    def _update_outdoor_temperature(self, log_update=True, log_initial=False):
        if self.outdoor_temp_service_name:
            temp_c, is_error = self._get_dbus_value(self.outdoor_temp_service_name, TEMPERATURE_PATH)
            if temp_c is not None:
                self.outdoor_temp_fahrenheit = (temp_c * 9/5) + 32
                if log_initial:
                    logging.info(f"Initial Outdoor Temp: {self.outdoor_temp_fahrenheit:.1f}F")
                elif log_update:
                    logging.debug(f"Outdoor Temp: {self.outdoor_temp_fahrenheit:.1f}F")
            elif is_error:
                logging.debug(f"Outdoor temperature service {self.outdoor_temp_service_name} unavailable")
                self.outdoor_temp_service_name = None
        else:
            if log_initial:
                logging.info(f"No outdoor sensor - using default: {self.outdoor_temp_fahrenheit:.1f}F")
    
    def _update_altitude(self, log_update=True, log_initial=False):
        if self.gps_service_name:
            alt, is_error = self._get_dbus_value(self.gps_service_name, ALTITUDE_PATH)
            if alt is not None:
                try:
                    if isinstance(alt, dbus.Array):
                        alt_m = float(alt[0]) if alt else None
                    else:
                        alt_m = float(alt)
                    if alt_m is not None:
                        self.altitude_feet = alt_m * 3.28084
                        if log_initial:
                            logging.info(f"Initial Altitude: {self.altitude_feet:.0f}ft")
                        elif log_update:
                            logging.debug(f"Altitude: {self.altitude_feet:.0f}ft")
                except:
                    pass
            elif is_error:
                logging.debug(f"GPS service {self.gps_service_name} unavailable")
                self.gps_service_name = None
        else:
            if log_initial:
                logging.info(f"No GPS - using default altitude: {self.altitude_feet:.0f}ft")
    
    def _update_generator_temperature(self, log_update=True, log_initial=False):
        if self.generator_temp_service_name:
            temp_c, is_error = self._get_dbus_value(self.generator_temp_service_name, TEMPERATURE_PATH)
            if temp_c is not None:
                self.generator_temp_fahrenheit = (temp_c * 9/5) + 32
                if log_initial:
                    logging.info(f"Initial Generator Temp: {self.generator_temp_fahrenheit:.1f}F")
                elif log_update:
                    logging.debug(f"Generator Temp: {self.generator_temp_fahrenheit:.1f}F")
            elif is_error:
                logging.debug(f"Generator temperature service {self.generator_temp_service_name} unavailable")
                self.generator_temp_service_name = None
        else:
            if log_initial:
                logging.info(f"No gen temp sensor - using default: {self.generator_temp_fahrenheit:.1f}F")
    
    def _update_gen_auto_current_state(self, initial_read=False):
        if self.gen_auto_current_service:
            state, is_error = self._get_dbus_value(self.gen_auto_current_service, STATE_PATH)
            if state is not None:
                state = int(state)
                if initial_read:
                    self.gen_auto_current_state = state
                    self.previous_gen_auto_current_state = state
                    logging.info(f"Gen Auto Current: {'ON' if state == GEN_AUTO_CURRENT_ON else 'OFF'}")
                elif state != self.previous_gen_auto_current_state:
                    old_state = self.previous_gen_auto_current_state
                    self.previous_gen_auto_current_state = self.gen_auto_current_state
                    self.gen_auto_current_state = state
                    logging.info(f"Gen Auto Current changed from {'ON' if old_state == GEN_AUTO_CURRENT_ON else 'OFF'} to {'ON' if state == GEN_AUTO_CURRENT_ON else 'OFF'}")
                    
                    # If changed from OFF to ON and startup is complete, force derating immediately
                    if old_state != GEN_AUTO_CURRENT_ON and state == GEN_AUTO_CURRENT_ON and self.startup_sync_complete:
                        logging.info("Gen Auto Current enabled - forcing immediate derating")
                        GLib.idle_add(self._force_derating)
                else:
                    self.gen_auto_current_state = state
            elif is_error and not initial_read:
                # Service became unavailable
                logging.debug(f"Gen Auto Current service {self.gen_auto_current_service} unavailable")
                self.gen_auto_current_service = None
        elif not initial_read:
            # Periodically try to rediscover
            self._find_gen_auto_current_input_internal()
        
        if initial_read and not self.gen_auto_current_service:
            logging.info("Gen Auto Current input not found - derating disabled")
    
    def _force_derating(self):
        """Force derating to run immediately on both active and saved generator limits"""
        if not self.startup_sync_complete:
            logging.debug("Startup not complete - skipping force derating")
            return
        
        if self.transfer_state != TransferState.IDLE:
            logging.debug("Transfer in progress - delaying force derating")
            # Try again in 1 second
            GLib.timeout_add_seconds(1, self._force_derating)
            return
        
        logging.info("Executing force derating update")
        
        if self._is_generator_running():
            # Generator is running - update both active limit and saved generator limit
            self._perform_derating(AC_ACTIVE_INPUT_CURRENT_LIMIT_PATH, force=True)
            self._perform_derating(GENERATOR_CURRENT_LIMIT_PATH, force=True)
        else:
            # Generator not running - only update saved generator limit
            self._perform_derating(GENERATOR_CURRENT_LIMIT_PATH, force=True)
    
    def _is_generator_running(self):
        if self.transfer_switch_service:
            state, _ = self._get_dbus_value(self.transfer_switch_service, STATE_PATH)
            return state in GENERATOR_ON_VALUE if state else False
        return False
    
    def calculate_derating_factor(self, temp_f, alt_ft, gen_temp_f):
        """Calculate derated output - EXACT match to original script"""
        temperature_multiplier = 1.0
        altitude_multiplier = 1.0
        generator_temp_multiplier = 1.0
        
        if temp_f is not None:
            if temp_f > self.BASE_TEMPERATURE_THRESHOLD_F:
                temp_diff = temp_f - self.BASE_TEMPERATURE_THRESHOLD_F
                temperature_multiplier = 1.0 - (temp_diff * self.TEMP_COEFFICIENT)
                if temperature_multiplier < 0.0:
                    temperature_multiplier = 0.0
        
        if alt_ft is not None:
            altitude_multiplier = 1.0 - (alt_ft * self.ALTITUDE_COEFFICIENT)
            if altitude_multiplier < 0.0:
                altitude_multiplier = 0.0
        
        if gen_temp_f is not None:
            if gen_temp_f >= self.HIGH_GENTEMP_THRESHOLD_F:
                generator_temp_multiplier = self.HIGH_GENTEMP_REDUCTION
            elif gen_temp_f >= self.MEDIUM_GENTEMP_THRESHOLD_F:
                generator_temp_multiplier = self.MEDIUM_GENTEMP_REDUCTION
        
        # Calculate in the exact same order as original script
        # Original: derated_output_amps = BASE_GENERATOR_OUTPUT_AMPS * temp_mult * alt_mult * gen_temp_mult * OUTPUT_BUFFER
        derated = self.BASE_GENERATOR_OUTPUT_AMPS
        derated = derated * temperature_multiplier
        derated = derated * altitude_multiplier
        derated = derated * generator_temp_multiplier
        derated = derated * self.OUTPUT_BUFFER
        
        # Round to 1 decimal place
        rounded = round(derated, 1)
        
        # Debug logging
        logging.debug(f"Derating calc: {self.BASE_GENERATOR_OUTPUT_AMPS} * {temperature_multiplier:.6f} * {altitude_multiplier:.6f} * {generator_temp_multiplier} * {self.OUTPUT_BUFFER} = {derated:.4f} -> {rounded:.1f}A")
        
        return rounded
    
    def _perform_derating(self, target_path, force=False):
        """Calculate derated value and write to specified D-Bus path"""
        # Don't perform derating until startup is complete
        if not self.startup_sync_complete:
            return
        
        # Skip if a transfer is in progress (check state only, not lock)
        if self.transfer_state != TransferState.IDLE:
            logging.debug("Transfer in progress - skipping derating")
            return
        
        try:
            # Calculate derated value using the exact method
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
            
            # Use small threshold for comparison
            if current is None or abs(float(current) - derated) > 0.05 or force:
                self._set_dbus_value(service, target_path, derated)
                logging.info(f"{desc} updated to {derated}A (derated){' - FORCED' if force else ''}")
                
                # Update last known values to prevent duplicate sync
                if target_path == GENERATOR_CURRENT_LIMIT_PATH:
                    self.last_derated_gen_setting = derated
                else:
                    self.last_derated_active_limit = derated
                    # Also update the last derated gen setting to match if we're writing to active limit
                    if self.gen_auto_current_state == GEN_AUTO_CURRENT_ON and self._is_generator_running():
                        if self.last_derated_gen_setting != derated:
                            self.last_derated_gen_setting = derated
                    
        except Exception as e:
            logging.error(f"Derating calculation failed: {e}")
    
    def settings_changed(self, setting, old_value, new_value):
        # Skip during startup
        if not self.startup_sync_complete:
            return
        
        # Skip if a transfer is in progress
        if self.transfer_state != TransferState.IDLE:
            logging.debug(f"Transfer in progress - ignoring {setting} change")
            return
        
        logging.debug(f"Setting {setting}: {old_value} -> {new_value}")
        
        # If Gen Auto Current is ON, override changes to saved generator limit
        if self.gen_auto_current_state == GEN_AUTO_CURRENT_ON:
            if setting == 'generatorCurrentLimit':
                logging.info(f"Gen Auto ON - overriding generator saved limit change from {old_value}A to {new_value}A")
                GLib.idle_add(lambda: self._perform_derating(GENERATOR_CURRENT_LIMIT_PATH, force=True))
                # If generator is running, also override active limit
                if self._is_generator_running():
                    GLib.idle_add(lambda: self._perform_derating(AC_ACTIVE_INPUT_CURRENT_LIMIT_PATH, force=True))
                return
        
        # Normal handling for when Gen Auto Current is OFF
        if setting == 'generatorCurrentLimit' and self.dbusOk and self.transferSwitchActive:
            try:
                inp = self.acInputTypeObj.GetValue() if self.acInputTypeObj else None
                if inp == 2 and self.currentLimitIsAdjustableObj and self.currentLimitIsAdjustableObj.GetValue() == 1:
                    logging.info(f"Applying gen limit {new_value}A to active")
                    self.currentLimitObj.SetValue(wrap_dbus_value(new_value))
                    # Update last known value
                    self.last_derated_active_limit = new_value
            except Exception as e:
                logging.error(f"Failed to apply gen limit: {e}")
        
        elif setting == 'gridCurrentLimit' and self.dbusOk and self.transferSwitchActive:
            try:
                inp = self.acInputTypeObj.GetValue() if self.acInputTypeObj else None
                if inp in (1, 3) and self.currentLimitIsAdjustableObj and self.currentLimitIsAdjustableObj.GetValue() == 1:
                    logging.info(f"Applying grid limit {new_value}A to active")
                    self.currentLimitObj.SetValue(wrap_dbus_value(new_value))
                    # Update last known value
                    self.last_derated_active_limit = new_value
            except Exception as e:
                logging.error(f"Failed to apply grid limit: {e}")
    
    def verify_settings_change(self, expected_type, expected_limit, source):
        for attempt in range(5):
            try:
                actual_type = self.acInputTypeObj.GetValue()
                actual_limit = self.currentLimitObj.GetValue() if self.currentLimitIsAdjustableObj and self.currentLimitIsAdjustableObj.GetValue() == 1 else None
                
                if actual_type == expected_type and (actual_limit is None or abs(actual_limit - expected_limit) <= 0.5):
                    logging.info(f"✓ {source} verified (type={actual_type}, limit={actual_limit})")
                    return True
                
                logging.warning(f"Retry {attempt+1}/5 for {source}")
                if actual_type != expected_type:
                    self.acInputTypeObj.SetValue(wrap_dbus_value(expected_type))
                if actual_limit and abs(actual_limit - expected_limit) > 0.5:
                    self.currentLimitObj.SetValue(wrap_dbus_value(expected_limit))
                time.sleep(1)
            except Exception as e:
                logging.error(f"Verification error: {e}")
        
        logging.error(f"✗ {source} verification failed")
        return False
    
    def transfer_to_generator(self, lock_holder=None):
        """Transfer to generator - assumes lock is already held by caller"""
        if not self.dbusOk or not self.transferSwitchActive:
            return False
        
        # Verify lock is held by the caller
        if lock_holder is None or not self.transfer_lock.is_held_by(lock_holder):
            logging.error("transfer_to_generator called without lock being held")
            return False
        
        try:
            self.transfer_state = TransferState.TRANSFERRING_TO_GENERATOR
            logging.info("=== ATOMIC TRANSFER: Switching to GENERATOR ===")
            
            # Get the target limit BEFORE making any changes
            target_limit = self.DbusSettings['generatorCurrentLimit']
            target_type = 2
            
            # CRITICAL: Change BOTH settings in quick succession
            logging.info(f"Applying generator input type: {target_type}")
            self.acInputTypeObj.SetValue(wrap_dbus_value(target_type))
            
            if self.currentLimitIsAdjustableObj and self.currentLimitIsAdjustableObj.GetValue() == 1:
                logging.info(f"Applying generator current limit: {target_limit}A")
                self.currentLimitObj.SetValue(wrap_dbus_value(target_limit))
                # Update last known derated value
                self.last_derated_active_limit = target_limit
            
            # Verify both changes took effect
            success = self.verify_settings_change(target_type, target_limit, "Generator")
            
            if success:
                logging.info("=== ATOMIC TRANSFER: Generator transfer COMPLETE ===")
            else:
                logging.error("=== ATOMIC TRANSFER: Generator transfer VERIFICATION FAILED ===")
            
            return success
            
        except Exception as e:
            logging.error(f"Failed to apply generator settings: {e}")
            return False
        finally:
            self.transfer_state = TransferState.IDLE
    
    def transfer_to_grid(self, lock_holder=None):
        """Initiate transfer to grid - assumes lock is already held by caller"""
        if not self.dbusOk or not self.transferSwitchActive:
            return False
        
        # Verify lock is held by the caller
        if lock_holder is None or not self.transfer_lock.is_held_by(lock_holder):
            logging.error("transfer_to_grid called without lock being held")
            return False
        
        try:
            self.transfer_state = TransferState.WAITING_FOR_GENERATOR_SHUTDOWN
            logging.info(f"=== ATOMIC TRANSFER: Generator shutdown initiated - waiting {self.SHUTDOWN_TIMER_SECONDS}s ===")
            
            # Schedule the actual grid transfer after shutdown timer
            # Pass the lock holder name so it can be released later
            GLib.timeout_add_seconds(int(self.SHUTDOWN_TIMER_SECONDS), self._execute_grid_transfer, lock_holder)
            return True
        except Exception as e:
            logging.error(f"Failed to initiate grid transfer: {e}")
            self.transfer_state = TransferState.IDLE
            return False
    
    def _execute_grid_transfer(self, lock_holder):
        """Execute the actual grid transfer after generator shutdown - lock is already held"""
        try:
            self.transfer_state = TransferState.TRANSFERRING_TO_GRID
            logging.info("=== ATOMIC TRANSFER: Executing transfer to GRID ===")
            
            # Handle IgnoreAcIn1 if needed
            try:
                ignore = self.ignoreAcIn1Obj.GetValue() if self.ignoreAcIn1Obj else 0
                if ignore == 1:
                    logging.info("Disabling IgnoreAcIn1")
                    self.ignoreAcIn1Obj.SetValue(wrap_dbus_value(0))
                    time.sleep(1)
            except Exception as e:
                logging.error(f"IgnoreAcIn1 handling failed: {e}")
            
            # Get target values BEFORE making changes
            target_type = self.DbusSettings['gridInputType']
            target_limit = self.DbusSettings['gridCurrentLimit']
            
            # CRITICAL: Change BOTH settings in quick succession
            logging.info(f"Applying grid input type: {target_type}")
            self.acInputTypeObj.SetValue(wrap_dbus_value(target_type))
            
            if self.currentLimitIsAdjustableObj and self.currentLimitIsAdjustableObj.GetValue() == 1:
                logging.info(f"Applying grid current limit: {target_limit}A")
                self.currentLimitObj.SetValue(wrap_dbus_value(target_limit))
                # Update last known derated value
                self.last_derated_active_limit = target_limit
            
            # Verify both changes took effect
            self.verify_settings_change(target_type, target_limit, "Grid")
            
            logging.info("=== ATOMIC TRANSFER: Grid transfer COMPLETE ===")
            
        except Exception as e:
            logging.error(f"Grid transfer failed: {e}")
        finally:
            self.transfer_state = TransferState.IDLE
            # Release the lock that was acquired by the caller
            self.transfer_lock.release(lock_holder)
        
        return False
    
    def update_transfer_switch_state(self):
        """Update transfer switch state - reads from D-Bus and updates self.onGenerator"""
        if not self.transferSwitchActive or not self.transferSwitchStateObj:
            return
        
        try:
            state = self.transferSwitchStateObj.GetValue()
            if state in (12, 3):
                self.onGenerator = True
            elif state in (13, 2):
                self.onGenerator = False
            else:
                logging.debug(f"Unknown transfer switch state: {state}")
        except Exception as e:
            logging.debug(f"Error updating transfer switch state: {e}")
    
    def apply_debounced_state(self):
        if self.pending_generator_state is not None:
            self.onGenerator = self.pending_generator_state
            logging.info(f"State confirmed: {'GENERATOR' if self.onGenerator else 'GRID'}")
            self.pending_generator_state = None
            self.debounce_timer = None
        return False
    
    def search_for_transfer_switch_input(self):
        for service in self.bus.list_names():
            if service.startswith("com.victronenergy.digitalinput"):
                try:
                    name_obj = self.bus.get_object(service, '/CustomName')
                    name = name_obj.GetValue()
                    if self.extTransferDigInputName.lower() in name.lower():
                        state_obj = self.bus.get_object(service, '/State')
                        state = state_obj.GetValue()
                        if state in (12, 3, 13, 2):
                            self.transferSwitchNameObj = name_obj
                            self.transferSwitchStateObj = state_obj
                            self.transferSwitchActive = True
                            logging.info(f"Found transfer switch at {service} with name '{name}'")
                            return
                except Exception as e:
                    logging.debug(f"Error checking service {service}: {e}")
        
        if not self.firstSearchDone:
            logging.warning(f"No transfer switch found (name pattern: '{self.extTransferDigInputName}')")
            self.firstSearchDone = True
    
    def validate_settings(self):
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
    
    def update_remote_generator_selected(self):
        if self.remoteGeneratorSelectedItem is None:
            return
        
        new_val = 1 if (self.dbusOk and self.onGenerator) else 0
        if new_val != self.remoteGeneratorSelectedLocalValue:
            try:
                self.remoteGeneratorSelectedItem.SetValue(wrap_dbus_value(new_val))
                self.remoteGeneratorSelectedLocalValue = new_val
            except:
                pass
    
    def background(self):
        """Main background loop - runs every second"""
        if not self.startup_sync_complete:
            return True
        
        # Small delay after startup to let everything settle
        if not self.startup_settle_done:
            logging.info("Allowing 2 seconds for system to settle after startup...")
            time.sleep(2)
            self.startup_settle_done = True
        
        self.update_transfer_switch_state()
        
        # Check health of existing services and rediscover if needed
        self._check_service_health()
        
        # Rediscover optional services if not found
        if not self.outdoor_temp_service_name:
            self._find_outdoor_temperature_service()
        if not self.generator_temp_service_name:
            self._find_generator_temperature_service()
        if not self.gps_service_name:
            self._find_gps_service_internal()
        if not self.gen_auto_current_service:
            self._find_gen_auto_current_input_internal()
        
        # Also check if transfer switch service is still valid
        if self.transferSwitchActive and self.transferSwitchStateObj:
            try:
                # Test if service still responds
                self.transferSwitchStateObj.GetValue()
            except:
                logging.warning("Transfer switch service became unavailable, re-discovering")
                self.transferSwitchActive = False
                self.transferSwitchNameObj = None
                self.transferSwitchStateObj = None
                self._find_transfer_switch_input_internal()
        
        # Check if VE.Bus service is still valid
        if self.vebus_service and self.dbusOk:
            try:
                # Test if service still responds
                self.acInputTypeObj.GetValue()
            except:
                logging.warning("VE.Bus service became unavailable, re-discovering")
                self.vebus_service = None
                self.dbusOk = False
                self._find_vebus_service()
        
        # Update sensor values
        self._update_outdoor_temperature()
        self._update_altitude()
        self._update_generator_temperature()
        self._update_gen_auto_current_state()
        
        # Validate settings periodically
        if time.time() - self.last_validation > 300:
            self.validate_settings()
            self.last_validation = time.time()
        
        # DYNAMIC SYNC - Active to Saved (only when idle and not transferring)
        if self.dbusOk and self.transferSwitchActive and self.currentLimitObj and self.transfer_state == TransferState.IDLE and not self.transfer_lock.is_locked:
            try:
                current_input_type = self.acInputTypeObj.GetValue()
                current_limit = self.currentLimitObj.GetValue()
                
                if current_input_type == 2:
                    # On generator - only sync if Gen Auto Current is OFF
                    if self.gen_auto_current_state != GEN_AUTO_CURRENT_ON:
                        if abs(current_limit - self.DbusSettings['generatorCurrentLimit']) > 0.1:
                            logging.info(f"SYNC: Generator limit {self.DbusSettings['generatorCurrentLimit']:.1f}A -> {current_limit:.1f}A")
                            self.DbusSettings['generatorCurrentLimit'] = current_limit
                    else:
                        logging.debug("Gen Auto ON - skipping generator limit sync")
                elif current_input_type in (1, 3):
                    # On grid/shore - ALWAYS sync (Gen Auto doesn't affect grid)
                    if abs(current_limit - self.DbusSettings['gridCurrentLimit']) > 0.1:
                        logging.info(f"SYNC: Grid limit {self.DbusSettings['gridCurrentLimit']:.1f}A -> {current_limit:.1f}A")
                        self.DbusSettings['gridCurrentLimit'] = current_limit
            except Exception as e:
                logging.error(f"Dynamic sync failed: {e}")
        
        # Auto derating - runs every second when Gen Auto Current is ON
        if self.gen_auto_current_state == GEN_AUTO_CURRENT_ON and self.transfer_state == TransferState.IDLE:
            if self._is_generator_running():
                # When generator is running, update both active limit and saved generator limit
                self._perform_derating(AC_ACTIVE_INPUT_CURRENT_LIMIT_PATH, force=False)
                self._perform_derating(GENERATOR_CURRENT_LIMIT_PATH, force=False)
            else:
                # When generator is not running, only update the saved generator limit
                self._perform_derating(GENERATOR_CURRENT_LIMIT_PATH, force=False)
        
        # Handle transfer switch state changes - acquire lock and then call transfer functions
        if self.dbusOk and self.transferSwitchActive:
            if self.lastOnGenerator is None:
                self.lastOnGenerator = self.onGenerator
            elif self.onGenerator != self.lastOnGenerator:
                if self.onGenerator:
                    # Acquire lock and then transfer to generator
                    if self.transfer_lock.acquire("state_change", timeout=2):
                        try:
                            self.transfer_to_generator("state_change")
                        finally:
                            self.transfer_lock.release("state_change")
                    else:
                        logging.warning("Could not acquire lock for generator transfer, will retry next cycle")
                else:
                    # Acquire lock and then transfer to grid (lock will be released in _execute_grid_transfer)
                    if self.transfer_lock.acquire("state_change", timeout=2):
                        try:
                            self.transfer_to_grid("state_change")
                        except Exception as e:
                            logging.error(f"Error during grid transfer: {e}")
                            self.transfer_lock.release("state_change")
                    else:
                        logging.warning("Could not acquire lock for grid transfer, will retry next cycle")
            self.lastOnGenerator = self.onGenerator
        elif self.onGenerator:
            # Fallback - acquire lock and transfer to grid
            if self.transfer_lock.acquire("fallback", timeout=2):
                try:
                    self.transfer_to_grid("fallback")
                except Exception as e:
                    logging.error(f"Error during fallback grid transfer: {e}")
                    self.transfer_lock.release("fallback")
        
        self.update_remote_generator_selected()
        
        return True

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
    from dbus.mainloop.glib import DBusGMainLoop
    DBusGMainLoop(set_as_default=True)
    setup_logging()
    
    logging.info("=" * 60)
    logging.info("Dynamic Transfer Switch Monitor starting")
    logging.info("=" * 60)
    
    DynamicTransferSwitch()
    
    GLib.MainLoop().run()

if __name__ == "__main__":
    main()
