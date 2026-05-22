#!/usr/bin/env python3

"""
Dynamic Transfer Switch and Generator Auto Current Derating Monitor
Combined transfer switch management with generator current derating

Features:
- Atomic transfers with complete operation dropping
- Signal-based monitoring for instant response
- Two-way current limit sync with derating override
- Configurable shutdown timer and sensor buffers
- GPS altitude buffering to ignore small changes
- Temperature buffering to prevent unnecessary recalculations

Config file: /data/apps/dynamic_transferswitch/config.ini
"""

import platform
import argparse
import logging
import sys
import os
import time
import dbus
import configparser
from gi.repository import GLib
from dbus.mainloop.glib import DBusGMainLoop

sys.path.insert(1, "/opt/victronenergy/dbus-systemcalc-py/ext/velib_python")
from vedbus import VeDbusService
from ve_utils import wrap_dbus_value
from settingsdevice import SettingsDevice

# Logging setup
logger = logging.getLogger()
for handler in logger.handlers[:]:
    logger.removeHandler(handler)

formatter = logging.Formatter('%(asctime)s - %(name)s - %(levelname)s - %(message)s')
console_handler = logging.StreamHandler(sys.stdout)
console_handler.setFormatter(formatter)
logger.addHandler(console_handler)
logger.setLevel(logging.INFO)

# D-Bus paths
dbusSettingsPath = "com.victronenergy.settings"
dbusSystemPath = "com.victronenergy.system"
VEBUS_SERVICE_BASE = "com.victronenergy.vebus"
TEMPERATURE_SERVICE_BASE = "com.victronenergy.temperature"
GPS_SERVICE_BASE = "com.victronenergy.gps"
DIGITAL_INPUT_SERVICE_BASE = "com.victronenergy.digitalinput"

# Constants
GENERATOR_ON_VALUE = (12, 3)
SHORE_POWER_ON_VALUE = (13, 2)
GEN_AUTO_CURRENT_ON = 3
GEN_AUTO_CURRENT_OFF = 2

# Config file path
CONFIG_FILE_PATH = '/data/apps/dynamic_transferswitch/config.ini'

class DynamicTransferSwitch:
    def __init__(self):
        self.theBus = dbus.SystemBus()
        
        # CRITICAL: Transfer lock - when True, NO other operations proceed
        self.transfer_active = False
        self.transfer_state = "IDLE"  # IDLE, TRANSFERRING_TO_GRID, TRANSFERRING_TO_GENERATOR
        self.derating_active = False  # Flag to prevent sync loops during derating
        
        # Transfer switch state
        self.onGenerator = False
        self.lastOnGenerator = None
        self.transferSwitchActive = False
        self.transferSwitchStateObj = None
        self.transferSwitchNameObj = None
        self.transfer_switch_service = None
        self.extTransferDigInputName = "transfer switch"
        
        # VE.Bus state
        self.vebus_service = None
        self.veBusService = ""
        self.numberOfAcInputs = 0
        self.dbusOk = False
        self.acInputTypeObj = None
        self.currentLimitIsAdjustableObj = None
        self.ignoreAcIn1Obj = None
        self.remoteGeneratorSelectedItem = None
        self.remoteGeneratorSelectedLocalValue = -1
        self.transferSwitchLocation = 0
        
        # Service discovery
        self.outdoor_temp_service_name = None
        self.generator_temp_service_name = None
        self.gps_service_name = None
        self.gen_auto_current_service = None
        self.gen_auto_current_state = None
        self.previous_gen_auto_current_state = None
        
        # Sensor values with buffers
        self.outdoor_temp_fahrenheit = 77.0
        self.altitude_feet = 1000.0
        self.generator_temp_fahrenheit = 180.0
        
        # Last values for change detection
        self.last_derated_value = None
        self.last_altitude_feet = None
        self.last_outdoor_temp_f = None
        self.last_generator_temp_f = None
        
        # Buffer thresholds (can be overridden by config)
        self.ALTITUDE_BUFFER_FEET = 50.0      # Ignore altitude changes < 50ft
        self.TEMP_BUFFER_F = 1.0              # Ignore temp changes < 1°F
        self.DERATING_DEBOUNCE_MS = 500       # Wait 500ms after last change
        
        # Debounce timer
        self.derating_debounce_timer = None
        
        # Shutdown timer retry tracking
        self.ignore_retry_count = 0
        self.ignore_retry_timer = None
        
        # Load configuration
        self._load_config()
        
        # Setup D-Bus settings
        self._setup_settings()
        
        # Service discovery tracking
        self.firstSearchDone = False
        self.veBusFoundInitially = False
        self.loggedVeBusInitialNotFound = False
        self.tsInputSearchDelay = 10
        self.startup_delay_complete = False
        self.signals_setup = False
        
        # Error logging flags
        self.altitude_warning_logged = False
        self.altitude_value_logged_after_warning = False
        self.altitude_dbus_error_logged = False
        self.altitude_dbus_value_logged_after_error = False
        self.generator_temp_warning_logged = False
        self.generator_temp_value_logged_after_warning = False
        self.outdoor_temp_warning_logged = False
        self.outdoor_temp_value_logged_after_warning = False
        
        # Initial derating flag
        self.initial_derated_output_logged = False
        self.initial_altitude = None
        self.initial_outdoor_temp = None
        self.initial_generator_temp = None
        
        # Validation timer
        self.last_validation = time.time()
        
        # Start delayed initialization
        GLib.timeout_add_seconds(5, self._delayed_initialization)
        
        # Run background task every second (for health monitoring only)
        GLib.timeout_add_seconds(1, self.background)
        
        logging.info("=" * 60)
        logging.info("Dynamic Transfer Switch Monitor Starting")
        logging.info(f"Config file: {CONFIG_FILE_PATH}")
        logging.info(f"Shutdown timer: {self.SHUTDOWN_TIMER} seconds")
        logging.info(f"Altitude buffer: {self.ALTITUDE_BUFFER_FEET}ft")
        logging.info(f"Temperature buffer: {self.TEMP_BUFFER_F}°F")
        logging.info("=" * 60)

    def _load_config(self):
        """Loads settings from config file"""
        config = configparser.ConfigParser()
        
        # Set default values first
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
        self.SHUTDOWN_TIMER = 5

        if not os.path.exists(CONFIG_FILE_PATH):
            logging.warning(f"Config file not found at {CONFIG_FILE_PATH}. Using default settings.")
            return

        try:
            config.read(CONFIG_FILE_PATH)
            logging.info(f"Successfully loaded settings from {CONFIG_FILE_PATH}")
            
            # Read DeratingConstants
            self.BASE_TEMPERATURE_THRESHOLD_F = config.getfloat('DeratingConstants', 'BaseTemperatureThresholdF', fallback=self.BASE_TEMPERATURE_THRESHOLD_F)
            self.TEMP_COEFFICIENT = config.getfloat('DeratingConstants', 'TempCoefficient', fallback=self.TEMP_COEFFICIENT)
            self.ALTITUDE_COEFFICIENT = config.getfloat('DeratingConstants', 'AltitudeCoefficient', fallback=self.ALTITUDE_COEFFICIENT)
            self.BASE_GENERATOR_OUTPUT_AMPS = config.getfloat('DeratingConstants', 'BaseGeneratorOutputAmps', fallback=self.BASE_GENERATOR_OUTPUT_AMPS)
            self.OUTPUT_BUFFER = config.getfloat('DeratingConstants', 'OutputBuffer', fallback=self.OUTPUT_BUFFER)
            self.HIGH_GENTEMP_THRESHOLD_F = config.getfloat('DeratingConstants', 'HighGenTempThresholdF', fallback=self.HIGH_GENTEMP_THRESHOLD_F)
            self.MEDIUM_GENTEMP_THRESHOLD_F = config.getfloat('DeratingConstants', 'MediumGenTempThresholdF', fallback=self.MEDIUM_GENTEMP_THRESHOLD_F)
            self.HIGH_GENTEMP_REDUCTION = config.getfloat('DeratingConstants', 'HighGenTempReduction', fallback=self.HIGH_GENTEMP_REDUCTION)
            self.MEDIUM_GENTEMP_REDUCTION = config.getfloat('DeratingConstants', 'MediumGenTempReduction', fallback=self.MEDIUM_GENTEMP_REDUCTION)
            
            # Read DefaultSensorValues
            self.DEFAULT_ALTITUDE_FEET = config.getfloat('DefaultSensorValues', 'DefaultAltitudeFeet', fallback=self.DEFAULT_ALTITUDE_FEET)
            self.DEFAULT_GENERATOR_TEMP_F = config.getfloat('DefaultSensorValues', 'DefaultGeneratorTempF', fallback=self.DEFAULT_GENERATOR_TEMP_F)
            self.DEFAULT_OUTDOOR_TEMP_F = config.getfloat('DefaultSensorValues', 'DefaultOutdoorTempF', fallback=self.DEFAULT_OUTDOOR_TEMP_F)
            
            # Read TransferSettings
            if config.has_section('TransferSettings'):
                self.SHUTDOWN_TIMER = config.getfloat('TransferSettings', 'shutdown_timer', fallback=self.SHUTDOWN_TIMER)
                self.ALTITUDE_BUFFER_FEET = config.getfloat('TransferSettings', 'altitude_buffer_ft', fallback=self.ALTITUDE_BUFFER_FEET)
                self.TEMP_BUFFER_F = config.getfloat('TransferSettings', 'temp_buffer_f', fallback=self.TEMP_BUFFER_F)
                self.DERATING_DEBOUNCE_MS = config.getint('TransferSettings', 'derating_debounce_ms', fallback=self.DERATING_DEBOUNCE_MS)
                logging.info(f"Loaded TransferSettings: shutdown_timer={self.SHUTDOWN_TIMER}s, altitude_buffer={self.ALTITUDE_BUFFER_FEET}ft, temp_buffer={self.TEMP_BUFFER_F}F, debounce={self.DERATING_DEBOUNCE_MS}ms")
            
            # Set initial values from defaults
            self.altitude_feet = self.DEFAULT_ALTITUDE_FEET
            self.generator_temp_fahrenheit = self.DEFAULT_GENERATOR_TEMP_F
            self.outdoor_temp_fahrenheit = self.DEFAULT_OUTDOOR_TEMP_F
            self.last_altitude_feet = self.DEFAULT_ALTITUDE_FEET
            self.last_outdoor_temp_f = self.DEFAULT_OUTDOOR_TEMP_F
            self.last_generator_temp_f = self.DEFAULT_GENERATOR_TEMP_F

        except (configparser.Error, ValueError) as e:
            logging.error(f"Error reading config file {CONFIG_FILE_PATH}: {e}. Using default settings.")

    def _setup_settings(self):
        """Setup D-Bus settings"""
        settingsList = {
            'gridCurrentLimit': [
                '/Settings/TransferSwitch/GridCurrentLimit',
                0.0,
                0.0,
                0.0
            ],
            'generatorCurrentLimit': [
                '/Settings/TransferSwitch/GeneratorCurrentLimit',
                0.0,
                0.0,
                0.0
            ],
            'gridInputType': [
                '/Settings/TransferSwitch/GridType',
                0,
                0,
                0
            ],
            'stopWhenAcAvailable': [
                '/Settings/TransferSwitch/StopWhenAcAvailable',
                0,
                0,
                0
            ],
            'stopWhenAcAvailableFp': [
                '/Settings/TransferSwitch/StopWhenAcAvailableFp',
                0,
                0,
                0
            ],
            'transferSwitchOnAc2': [
                '/Settings/TransferSwitch/TransferSwitchOnAc2',
                0,
                0,
                0
            ],
        }

        self.DbusSettings = SettingsDevice(
            bus=self.theBus,
            supportedSettings=settingsList,
            timeout=10,
            eventCallback=self.settings_changed
        )

        if self.DbusSettings['gridInputType'] == 2:
            logging.warning("grid input type was generator - resetting to grid")
            self.DbusSettings['gridInputType'] = 1

    def settings_changed(self, setting, old_value, new_value):
        """Callback when settings are changed via D-Bus"""
        logging.debug(f"Setting changed: {setting} = {new_value} (was {old_value})")
        
        # If stored generator limit changed externally and Auto Current is ON, recalculate derating
        if setting == 'generatorCurrentLimit' and self.gen_auto_current_state == GEN_AUTO_CURRENT_ON:
            logging.info(f"Stored generator limit changed externally to {new_value}A - checking derating")
            self._schedule_derating_recalculation()

    def _delayed_initialization(self):
        """Wait for D-Bus to stabilize before first search"""
        # Initial attempts to find services
        self._find_vebus_service()
        self._find_outdoor_temperature_service()
        self._find_generator_temperature_service()
        self._find_gps_service()
        self._find_gen_auto_current_input()
        self._find_transfer_switch_input()
        
        self._read_initial_values()
        self.startup_delay_complete = True
        logging.info("Startup delay complete - monitoring active")
        return GLib.SOURCE_REMOVE

    def _read_initial_values(self):
        """Read initial sensor and state values"""
        self._update_outdoor_temperature(log_initial=True)
        self._update_altitude(log_initial=True)
        self._update_generator_temperature(log_initial=True)
        self._update_gen_auto_current_state(initial_read=True)
        
        # Read current limits
        gen_limit = self.DbusSettings['generatorCurrentLimit']
        grid_limit = self.DbusSettings['gridCurrentLimit']
        logging.info(f"Initial Generator Current Limit: {gen_limit} Amps")
        logging.info(f"Initial Grid Current Limit: {grid_limit} Amps")
        
        if self.vebus_service:
            ac_limit, _ = self._get_dbus_value(self.vebus_service, "/Ac/ActiveIn/CurrentLimit")
            if ac_limit is not None:
                logging.info(f"Initial VE.Bus Active Current Limit: {round(float(ac_limit), 1)} Amps")
        
        # Initial derating calculation
        if self.gen_auto_current_state == GEN_AUTO_CURRENT_ON:
            self._schedule_derating_recalculation()

    def _find_service(self, service_base):
        """Find first service matching base name"""
        services = [name for name in self.theBus.list_names() if name.startswith(service_base)]
        return services[0] if services else None

    def _find_vebus_service(self):
        """Discover VE.Bus service"""
        self.vebus_service = self._find_service(VEBUS_SERVICE_BASE)
        if self.vebus_service:
            logging.info(f"Found VE.Bus service: {self.vebus_service}")
            self._setup_vebus_objects()
            self._setup_vebus_signals()
        else:
            logging.warning("VE.Bus service not found")

    def _setup_vebus_objects(self):
        """Setup VE.Bus D-Bus objects"""
        try:
            self.numberOfAcInputs = self._get_dbus_value(self.vebus_service, "/Ac/NumberOfAcInputs")[0]
            self.currentLimitIsAdjustableObj = self.theBus.get_object(self.vebus_service, "/Ac/ActiveIn/CurrentLimitIsAdjustable")
            self.ignoreAcIn1Obj = self.theBus.get_object(self.vebus_service, "/Ac/Control/IgnoreAcIn1")
            
            # Setup AC input type object based on transfer switch location
            if self.numberOfAcInputs == 2 and self.DbusSettings['transferSwitchOnAc2'] == 1:
                self.acInputTypeObj = self.theBus.get_object(dbusSettingsPath, "/Settings/SystemSetup/AcInput2")
                self.transferSwitchLocation = 2
                logging.info("Transfer switch on AC input 2 (Quattro)")
            else:
                self.acInputTypeObj = self.theBus.get_object(dbusSettingsPath, "/Settings/SystemSetup/AcInput1")
                self.transferSwitchLocation = 1
                logging.info("Transfer switch on AC input 1")
                
            self.dbusOk = True
        except Exception as e:
            logging.error(f"Failed to setup VE.Bus objects: {e}")
            self.dbusOk = False

    def _setup_vebus_signals(self):
        """Setup signals for VE.Bus monitoring"""
        if not self.vebus_service:
            return
        
        try:
            # Monitor active current limit changes for two-way sync
            current_limit_obj = self.theBus.get_object(
                self.vebus_service, "/Ac/ActiveIn/CurrentLimit"
            )
            current_limit_obj.connect_to_signal(
                "PropertiesChanged",
                self._on_current_limit_signal,
                dbus_interface="org.freedesktop.DBus.Properties"
            )
            logging.info("Current limit signal active for two-way sync")
        except Exception as e:
            logging.debug(f"Failed to setup VE.Bus signals: {e}")

    def _find_outdoor_temperature_service(self):
        """Discover outdoor temperature sensor and setup signal"""
        self.outdoor_temp_service_name = None
        temperature_services = [name for name in self.theBus.list_names() if name.startswith(TEMPERATURE_SERVICE_BASE)]
        for service_name in temperature_services:
            try:
                custom_name = self._get_dbus_value(service_name, "/CustomName")[0]
                if custom_name and "Outdoor" in str(custom_name):
                    self.outdoor_temp_service_name = service_name
                    logging.info(f"Found outdoor temperature service: {service_name}")
                    self._setup_temperature_signal(service_name, "outdoor")
                    return
            except:
                pass

    def _find_generator_temperature_service(self):
        """Discover generator temperature sensor and setup signal"""
        self.generator_temp_service_name = None
        temperature_services = [name for name in self.theBus.list_names() if name.startswith(TEMPERATURE_SERVICE_BASE)]
        for service_name in temperature_services:
            try:
                custom_name = self._get_dbus_value(service_name, "/CustomName")[0]
                product_name = self._get_dbus_value(service_name, "/ProductName")[0]
                if (custom_name and any(keyword in str(custom_name).lower() for keyword in ["gen", "generator"])) or \
                   (product_name and any(keyword in str(product_name).lower() for keyword in ["gen", "generator"])):
                    self.generator_temp_service_name = service_name
                    logging.info(f"Found generator temperature service: {service_name}")
                    self._setup_temperature_signal(service_name, "generator")
                    return
            except:
                pass

    def _setup_temperature_signal(self, service_name, sensor_type):
        """Setup signal monitoring for temperature sensor"""
        try:
            temp_obj = self.theBus.get_object(service_name, "/Temperature")
            temp_obj.connect_to_signal(
                "PropertiesChanged",
                self._on_temperature_changed,
                dbus_interface="org.freedesktop.DBus.Properties"
            )
            logging.info(f"Temperature signal active for {sensor_type} sensor")
        except Exception as e:
            logging.debug(f"Failed to setup temperature signal for {service_name}: {e}")

    def _find_gps_service(self):
        """Discover GPS service and setup signal"""
        self.gps_service_name = self._find_service(GPS_SERVICE_BASE)
        if self.gps_service_name:
            logging.info(f"Found GPS service: {self.gps_service_name}")
            self._setup_gps_signal()
        else:
            logging.warning("GPS service not found")

    def _setup_gps_signal(self):
        """Setup signal monitoring for GPS altitude"""
        if not self.gps_service_name:
            return
        
        try:
            gps_obj = self.theBus.get_object(self.gps_service_name, "/Altitude")
            gps_obj.connect_to_signal(
                "PropertiesChanged",
                self._on_altitude_changed,
                dbus_interface="org.freedesktop.DBus.Properties"
            )
            logging.info(f"GPS altitude signal active with {self.ALTITUDE_BUFFER_FEET}ft buffer")
        except Exception as e:
            logging.debug(f"Failed to setup GPS signal: {e}")

    def _find_gen_auto_current_input(self):
        """Discover Gen Auto Current digital input and setup signal"""
        self.gen_auto_current_service = None
        service_names = [name for name in self.theBus.list_names() if name.startswith(DIGITAL_INPUT_SERVICE_BASE)]
        for service_name in service_names:
            try:
                product_name = self._get_dbus_value(service_name, "/ProductName")[0]
                if product_name and ("Gen Auto Current" in str(product_name) or "gen auto current" in str(product_name)):
                    self.gen_auto_current_service = service_name
                    logging.info(f"Found Gen Auto Current input: {service_name}")
                    self._setup_gen_auto_current_signal()
                    return
            except:
                pass

    def _setup_gen_auto_current_signal(self):
        """Setup signal monitoring for Gen Auto Current switch"""
        if not self.gen_auto_current_service:
            return
        
        try:
            state_obj = self.theBus.get_object(self.gen_auto_current_service, "/State")
            state_obj.connect_to_signal(
                "PropertiesChanged",
                self._on_gen_auto_current_signal,
                dbus_interface="org.freedesktop.DBus.Properties"
            )
            logging.info("Gen Auto Current signal active")
        except Exception as e:
            logging.debug(f"Failed to setup Gen Auto Current signal: {e}")

    def _find_transfer_switch_input(self):
        """Discover transfer switch digital input and setup signal"""
        self.transfer_switch_service = None
        service_names = [name for name in self.theBus.list_names() if name.startswith(DIGITAL_INPUT_SERVICE_BASE)]
        for service_name in service_names:
            try:
                custom_name = self._get_dbus_value(service_name, "/CustomName")[0]
                if custom_name and self.extTransferDigInputName.lower() in str(custom_name).lower():
                    state = self._get_dbus_value(service_name, "/State")[0]
                    if state in GENERATOR_ON_VALUE or state in SHORE_POWER_ON_VALUE:
                        self.transfer_switch_service = service_name
                        self.transferSwitchActive = True
                        self.onGenerator = state in GENERATOR_ON_VALUE
                        self.lastOnGenerator = self.onGenerator
                        logging.info(f"Found transfer switch at {service_name} with name '{custom_name}', state={'Generator' if self.onGenerator else 'Grid'}")
                        self._setup_transfer_switch_signal()
                        return
            except:
                pass
        
        if not self.firstSearchDone:
            logging.warning("No transfer switch input found with matching custom name")
            self.firstSearchDone = True

    def _setup_transfer_switch_signal(self):
        """Setup signal monitoring for transfer switch digital input"""
        if not self.transfer_switch_service:
            return
        
        try:
            state_obj = self.theBus.get_object(self.transfer_switch_service, "/State")
            state_obj.connect_to_signal(
                "PropertiesChanged",
                self._on_transfer_switch_signal,
                dbus_interface="org.freedesktop.DBus.Properties"
            )
            logging.info(f"Transfer switch signal active for {self.transfer_switch_service}")
        except Exception as e:
            logging.error(f"Failed to setup transfer switch signal: {e}")

    def _get_dbus_value(self, service_name, path):
        """Get D-Bus value safely"""
        if not service_name:
            return None, False
        try:
            obj = self.theBus.get_object(service_name, path)
            interface = dbus.Interface(obj, "com.victronenergy.BusItem")
            return interface.GetValue(), False
        except dbus.exceptions.DBusException as e:
            error_message = str(e)
            is_service_unknown = "DBus.Error.ServiceUnknown" in error_message
            if not is_service_unknown:
                logging.error(f"D-Bus error getting value from {service_name}{path}: {e}")
            return None, is_service_unknown
        except Exception as e:
            logging.error(f"Unexpected error getting value from {service_name}{path}: {e}")
            return None, False

    def _set_dbus_value(self, service_name, path, value):
        """Set D-Bus value safely using wrap_dbus_value"""
        if not service_name:
            return
        try:
            obj = self.theBus.get_object(service_name, path)
            interface = dbus.Interface(obj, "com.victronenergy.BusItem")
            interface.SetValue(wrap_dbus_value(value))
            logging.debug(f"Set {service_name}{path} to {value}")
        except Exception as e:
            logging.error(f"Failed to set {path}: {e}")

    def _set_ac_input_type(self, input_type):
        """Set AC input type using wrap_dbus_value"""
        try:
            self.acInputTypeObj.SetValue(wrap_dbus_value(input_type))
            logging.debug(f"Set AC input type to {input_type}")
        except Exception as e:
            logging.error(f"Failed to set AC input type: {e}")

    def _update_outdoor_temperature(self, log_initial=False):
        """Initial read of outdoor temperature (signals handle updates)"""
        if self.outdoor_temp_service_name:
            temp_c, _ = self._get_dbus_value(self.outdoor_temp_service_name, "/Temperature")
            if temp_c is not None:
                self.outdoor_temp_fahrenheit = (float(temp_c) * 9/5) + 32
                self.last_outdoor_temp_f = self.outdoor_temp_fahrenheit
                if log_initial:
                    logging.info(f"Initial Outdoor Temperature: {self.outdoor_temp_fahrenheit:.1f}°F")

    def _update_altitude(self, log_initial=False):
        """Initial read of altitude (signals handle updates)"""
        if self.gps_service_name:
            altitude_raw, _ = self._get_dbus_value(self.gps_service_name, "/Altitude")
            if altitude_raw is not None:
                try:
                    if isinstance(altitude_raw, dbus.Array) and altitude_raw:
                        altitude_meters = float(altitude_raw[0])
                    else:
                        altitude_meters = float(altitude_raw)
                    self.altitude_feet = altitude_meters * 3.28084
                    self.last_altitude_feet = self.altitude_feet
                    if log_initial:
                        logging.info(f"Initial Altitude: {self.altitude_feet:.0f} feet")
                except (ValueError, TypeError) as e:
                    logging.debug(f"Error parsing altitude: {e}")

    def _update_generator_temperature(self, log_initial=False):
        """Initial read of generator temperature (signals handle updates)"""
        if self.generator_temp_service_name:
            temp_c, _ = self._get_dbus_value(self.generator_temp_service_name, "/Temperature")
            if temp_c is not None:
                self.generator_temp_fahrenheit = (float(temp_c) * 9/5) + 32
                self.last_generator_temp_f = self.generator_temp_fahrenheit
                if log_initial:
                    logging.info(f"Initial Generator Temperature: {self.generator_temp_fahrenheit:.1f}°F")

    def _update_gen_auto_current_state(self, initial_read=False):
        """Initial read of Gen Auto Current state (signals handle updates)"""
        if self.gen_auto_current_service:
            state, _ = self._get_dbus_value(self.gen_auto_current_service, "/State")
            if state is not None:
                self.gen_auto_current_state = int(state)
                if initial_read:
                    logging.info(f"Initial Gen Auto Current: {'ON' if self.gen_auto_current_state == GEN_AUTO_CURRENT_ON else 'OFF'}")

    def _is_generator_running(self):
        """Check if generator is running based on transfer switch"""
        if self.transfer_switch_service:
            state, _ = self._get_dbus_value(self.transfer_switch_service, "/State")
            return state in GENERATOR_ON_VALUE
        return False

    def _on_transfer_switch_signal(self, interface, changed_props, invalidated_props):
        """Called IMMEDIATELY when transfer switch state changes"""
        if 'Value' not in changed_props:
            return
        
        new_state = changed_props['Value']
        new_onGenerator = new_state in GENERATOR_ON_VALUE
        
        # Ignore if no change
        if new_onGenerator == self.onGenerator:
            return
        
        self.onGenerator = new_onGenerator
        logging.info(f"Signal: Transfer switch changed to {'Generator' if self.onGenerator else 'Grid'}")
        
        # Initiate transfer (atomic, drops all operations)
        if self.onGenerator:
            self.transfer_to_generator()
        else:
            self.transfer_to_grid()

    def _on_current_limit_signal(self, interface, changed_props, invalidated_props):
        """Called when active current limit changes (user or system)"""
        if self.derating_active or self.transfer_active:
            return  # Ignore if derating or transfer caused the change
        
        if 'Value' in changed_props:
            # User changed the limit - sync to stored
            logging.debug("Active current limit changed externally - syncing to stored")
            self.sync_active_to_stored()

    def _on_temperature_changed(self, interface, changed_props, invalidated_props):
        """Called when temperature changes - with buffer"""
        if 'Value' not in changed_props:
            return
        
        temp_c = changed_props['Value']
        temp_f = (float(temp_c) * 9/5) + 32
        
        # Determine which sensor and check buffer
        should_recalculate = False
        
        if self.outdoor_temp_service_name and interface.startswith(self.outdoor_temp_service_name):
            if self.last_outdoor_temp_f is None or abs(temp_f - self.last_outdoor_temp_f) >= self.TEMP_BUFFER_F:
                self.last_outdoor_temp_f = temp_f
                should_recalculate = True
                logging.debug(f"Outdoor temp changed: {temp_f:.1f}°F")
        
        elif self.generator_temp_service_name and interface.startswith(self.generator_temp_service_name):
            if self.last_generator_temp_f is None or abs(temp_f - self.last_generator_temp_f) >= self.TEMP_BUFFER_F:
                self.last_generator_temp_f = temp_f
                should_recalculate = True
                logging.debug(f"Generator temp changed: {temp_f:.1f}°F")
        
        if should_recalculate and self.gen_auto_current_state == GEN_AUTO_CURRENT_ON:
            self._schedule_derating_recalculation()

    def _on_altitude_changed(self, interface, changed_props, invalidated_props):
        """Called when GPS altitude changes - with buffer to ignore small changes"""
        if 'Value' not in changed_props:
            return
        
        altitude_raw = changed_props['Value']
        try:
            if isinstance(altitude_raw, dbus.Array) and altitude_raw:
                altitude_meters = float(altitude_raw[0])
            else:
                altitude_meters = float(altitude_raw)
            
            new_altitude_ft = altitude_meters * 3.28084
            
            # Only recalculate if change exceeds buffer
            if (self.last_altitude_feet is None or 
                abs(new_altitude_ft - self.last_altitude_feet) >= self.ALTITUDE_BUFFER_FEET):
                self.last_altitude_feet = new_altitude_ft
                logging.debug(f"Altitude changed: {new_altitude_ft:.0f}ft")
                if self.gen_auto_current_state == GEN_AUTO_CURRENT_ON:
                    self._schedule_derating_recalculation()
        except (ValueError, TypeError) as e:
            logging.debug(f"Error parsing altitude: {e}")

    def _on_gen_auto_current_signal(self, interface, changed_props, invalidated_props):
        """Called when Gen Auto Current switch toggles"""
        if 'Value' not in changed_props:
            return
        
        new_state = int(changed_props['Value'])
        self.gen_auto_current_state = new_state
        logging.info(f"Gen Auto Current changed to: {'ON' if new_state == GEN_AUTO_CURRENT_ON else 'OFF'}")
        
        # Immediately recalculate derating if turned ON
        if new_state == GEN_AUTO_CURRENT_ON:
            self._schedule_derating_recalculation()

    def calculate_derating_factor(self):
        """Calculate total derating factor - uses buffered sensor values"""
        temperature_multiplier = 1.0
        altitude_multiplier = 1.0
        generator_temp_multiplier = 1.0
        
        outdoor_temp = self.last_outdoor_temp_f if self.last_outdoor_temp_f is not None else self.outdoor_temp_fahrenheit
        altitude = self.last_altitude_feet if self.last_altitude_feet is not None else self.altitude_feet
        generator_temp = self.last_generator_temp_f if self.last_generator_temp_f is not None else self.generator_temp_fahrenheit
        
        if outdoor_temp is not None:
            if outdoor_temp > self.BASE_TEMPERATURE_THRESHOLD_F:
                temperature_multiplier = 1.0 - ((outdoor_temp - self.BASE_TEMPERATURE_THRESHOLD_F) * self.TEMP_COEFFICIENT)
                temperature_multiplier = max(0.0, temperature_multiplier)
        
        if altitude is not None:
            altitude_multiplier = 1.0 - (altitude * self.ALTITUDE_COEFFICIENT)
            altitude_multiplier = max(0.0, altitude_multiplier)
        
        if generator_temp is not None:
            if generator_temp >= self.HIGH_GENTEMP_THRESHOLD_F:
                generator_temp_multiplier = self.HIGH_GENTEMP_REDUCTION
            elif generator_temp >= self.MEDIUM_GENTEMP_THRESHOLD_F:
                generator_temp_multiplier = self.MEDIUM_GENTEMP_REDUCTION
        
        return temperature_multiplier * altitude_multiplier * generator_temp_multiplier * self.OUTPUT_BUFFER

    def _schedule_derating_recalculation(self):
        """Schedule derating recalculation with debouncing"""
        if self.derating_debounce_timer:
            GLib.source_remove(self.derating_debounce_timer)
        
        self.derating_debounce_timer = GLib.timeout_add(
            self.DERATING_DEBOUNCE_MS,
            self._recalculate_derating
        )

    def _recalculate_derating(self):
        """Recalculate derated value and apply if changed"""
        self.derating_debounce_timer = None
        
        # Skip during transfers
        if self.transfer_active:
            logging.debug("Transfer active - skipping derating recalculation")
            return
        
        # Only recalculate if Gen Auto Current is ON
        if self.gen_auto_current_state != GEN_AUTO_CURRENT_ON:
            return
        
        # Calculate new derated value
        derating_factor = self.calculate_derating_factor()
        derated_amps = self.BASE_GENERATOR_OUTPUT_AMPS * derating_factor
        rounded_output = round(derated_amps, 1)
        
        # Only apply if value changed
        if self.last_derated_value == rounded_output and self.last_derated_value is not None:
            logging.debug(f"Derated value unchanged: {rounded_output}A")
            return
        
        self.last_derated_value = rounded_output
        logging.info(f"Derated value: {rounded_output}A (factor: {derating_factor:.3f})")
        
        # Apply based on generator state
        generator_running = self._is_generator_running()
        
        if generator_running and self.dbusOk:
            # Case 1: Generator running - write to BOTH active AND stored
            self.derating_active = True
            
            # Write to active limit (immediate effect)
            current_active, _ = self._get_dbus_value(self.vebus_service, "/Ac/ActiveIn/CurrentLimit")
            if current_active is None or abs(float(current_active) - rounded_output) > 0.2:
                self._set_dbus_value(self.vebus_service, "/Ac/ActiveIn/CurrentLimit", rounded_output)
                logging.info(f"Derating: Active limit set to {rounded_output:.1f}A")
            
            # Write to stored limit (for next startup)
            if abs(rounded_output - self.DbusSettings['generatorCurrentLimit']) > 0.2:
                self.DbusSettings['generatorCurrentLimit'] = rounded_output
                logging.info(f"Derating: Stored generator limit synced to {rounded_output:.1f}A")
            
            self.derating_active = False
            
        elif not generator_running:
            # Case 2: Generator NOT running - write to stored limit only
            if abs(rounded_output - self.DbusSettings['generatorCurrentLimit']) > 0.2:
                self.DbusSettings['generatorCurrentLimit'] = rounded_output
                logging.info(f"Derating: Stored generator limit updated to {rounded_output:.1f}A")

    def sync_active_to_stored(self):
        """Sync active limit changes back to stored settings (user changes)"""
        if self.derating_active or self.transfer_active or not self.dbusOk:
            return
        
        try:
            current_input_type = self.acInputTypeObj.GetValue()
            active_limit, _ = self._get_dbus_value(self.vebus_service, "/Ac/ActiveIn/CurrentLimit")
            
            if active_limit is None:
                return
                
            active_limit = float(active_limit)
            
            if current_input_type == 2:  # On generator
                if abs(active_limit - self.DbusSettings['generatorCurrentLimit']) > 0.2:
                    logging.info(f"User changed active limit to {active_limit}A - syncing to stored generator limit")
                    self.DbusSettings['generatorCurrentLimit'] = active_limit
                    # Trigger derating recalculation to ensure safe limits
                    if self.gen_auto_current_state == GEN_AUTO_CURRENT_ON:
                        self._schedule_derating_recalculation()
            
            elif current_input_type in (1, 3):  # On grid/shore
                if abs(active_limit - self.DbusSettings['gridCurrentLimit']) > 0.2:
                    logging.info(f"User changed active limit to {active_limit}A - syncing to stored grid limit")
                    self.DbusSettings['gridCurrentLimit'] = active_limit
                    
        except Exception as e:
            logging.debug(f"Active to stored sync failed: {e}")

    def transfer_to_generator(self):
        """ATOMIC transfer to generator - DROP if already transferring"""
        if self.transfer_active:
            logging.warning("Transfer already active - DROPPING generator transfer request")
            return
        
        self.transfer_active = True
        self.transfer_state = "TRANSFERRING_TO_GENERATOR"
        logging.info("🔒 ATOMIC TRANSFER: Switching to generator - ALL operations DROPPED")
        
        try:
            if not self.dbusOk:
                logging.error("Cannot transfer - DBus not OK")
                return
            
            logging.info("Applying generator settings")
            self._set_ac_input_type(2)
            
            if self.currentLimitIsAdjustableObj.GetValue() == 1:
                gen_limit = self.DbusSettings['generatorCurrentLimit']
                logging.info(f"Applying generator current limit: {gen_limit}A")
                self._set_dbus_value(self.vebus_service, "/Ac/ActiveIn/CurrentLimit", gen_limit)
            
            time.sleep(0.5)
            logging.info("Generator transfer completed successfully")
            
        except Exception as e:
            logging.error(f"Failed to switch to generator: {e}")
        finally:
            self.transfer_active = False
            self.transfer_state = "IDLE"
            logging.info("🔓 ATOMIC TRANSFER COMPLETE: Operations resumed")

    def _check_ignore_ac_in1_with_retry(self):
        """Check IgnoreAcIn1 with retry mechanism (max 5 retries at 1 second intervals)"""
        try:
            ignore_state = self.ignoreAcIn1Obj.GetValue()
            if ignore_state == 1:
                self.ignore_retry_count += 1
                if self.ignore_retry_count <= 5:
                    logging.info(f"IgnoreAcIn1 enabled (attempt {self.ignore_retry_count}/5) - retry in 1s")
                    self.ignore_retry_timer = GLib.timeout_add_seconds(1, self._check_ignore_ac_in1_with_retry)
                    return True
                else:
                    logging.warning("IgnoreAcIn1 still enabled after 5 retries - proceeding anyway")
                    self._apply_grid_settings()
                    return False
            else:
                logging.info("IgnoreAcIn1 disabled - proceeding with grid transfer")
                self._apply_grid_settings()
                return False
        except Exception as e:
            logging.error(f"Error checking IgnoreAcIn1: {e}")
            self._apply_grid_settings()
            return False

    def transfer_to_grid(self):
        """ATOMIC transfer to grid with configurable timer and retry mechanism"""
        if self.transfer_active:
            logging.warning("Transfer already active - DROPPING grid transfer request")
            return
        
        self.transfer_active = True
        self.transfer_state = "TRANSFERRING_TO_GRID"
        self.ignore_retry_count = 0
        logging.info(f"🔒 ATOMIC TRANSFER: Switching to grid - ALL operations DROPPED for {self.SHUTDOWN_TIMER}s")
        
        def start_transfer():
            logging.info(f"Shutdown timer ({self.SHUTDOWN_TIMER}s) complete - beginning grid transfer")
            self._check_ignore_ac_in1_with_retry()
            return False
        
        GLib.timeout_add_seconds(self.SHUTDOWN_TIMER, start_transfer)

    def _apply_grid_settings(self):
        """Apply grid settings to inverter"""
        try:
            if self.ignore_retry_timer:
                GLib.source_remove(self.ignore_retry_timer)
                self.ignore_retry_timer = None
            
            logging.info("Applying grid settings")
            grid_type = self.DbusSettings['gridInputType']
            grid_limit = self.DbusSettings['gridCurrentLimit']
            
            self._set_ac_input_type(grid_type)
            
            if self.currentLimitIsAdjustableObj.GetValue() == 1:
                logging.info(f"Applying grid current limit: {grid_limit}A")
                self._set_dbus_value(self.vebus_service, "/Ac/ActiveIn/CurrentLimit", grid_limit)
            
            time.sleep(0.5)
            logging.info("Grid transfer completed successfully")
            
        except Exception as e:
            logging.error(f"Failed to apply grid settings: {e}")
        finally:
            self.transfer_active = False
            self.transfer_state = "IDLE"
            logging.info("🔓 ATOMIC TRANSFER COMPLETE: Operations resumed")

    def background(self):
        """Minimal background loop - for health monitoring only"""
        if not self.startup_delay_complete:
            return True
        
        # Discover services if still missing
        if not self.vebus_service:
            self._find_vebus_service()
        if not self.outdoor_temp_service_name:
            self._find_outdoor_temperature_service()
        if not self.generator_temp_service_name:
            self._find_generator_temperature_service()
        if not self.gps_service_name:
            self._find_gps_service()
        if not self.gen_auto_current_service:
            self._find_gen_auto_current_input()
        if not self.transfer_switch_service:
            self._find_transfer_switch_input()
        
        # Periodic health logging (every 5 minutes)
        if time.time() - self.last_validation > 300:
            gen_running = self._is_generator_running()
            logging.info(f"Status - Gen: {'ON' if gen_running else 'OFF'}, "
                        f"Transfer: {self.transfer_state}, "
                        f"Auto Current: {'ON' if self.gen_auto_current_state == GEN_AUTO_CURRENT_ON else 'OFF'}, "
                        f"Last Derated: {self.last_derated_value}A, "
                        f"Grid Limit: {self.DbusSettings['gridCurrentLimit']}A, "
                        f"Gen Limit: {self.DbusSettings['generatorCurrentLimit']}A, "
                        f"Temp: {self.last_outdoor_temp_f:.0f}°F, "
                        f"Alt: {self.last_altitude_feet:.0f}ft")
            self.last_validation = time.time()
        
        return True

def main():
    DBusGMainLoop(set_as_default=True)
    
    logging.info("=" * 60)
    logging.info("Dynamic Transfer Switch Monitor Starting")
    logging.info("Features: Signal-driven, Atomic transfers, Two-way sync, Sensor buffering")
    logging.info("=" * 60)
    
    DynamicTransferSwitch()
    
    mainloop = GLib.MainLoop()
    mainloop.run()

if __name__ == "__main__":
    main()