# coding=utf-8

from flask import render_template, flash, redirect, session, url_for, request, g, Markup, Flask
try:
    from urllib.parse import urlparse
except ImportError:
     from urlparse import urlparse
from ncclient import manager
from datetime import datetime
from collections import deque
from apscheduler.schedulers.background import BackgroundScheduler
from apscheduler.triggers.interval import IntervalTrigger
from pusher import Pusher
import requests, json, atexit, time, plotly, plotly.graph_objs as go
import xmltodict
import mysql.connector
from multiprocessing import Pool
from mysql.connector.pooling import MySQLConnectionPool
from mysql.connector import connect
import json
import copy
import threading
from json2html import *
from app import app

#pusher channel credentials
pusher = Pusher(
  app_id="826092",
  key="00a5e21b49f59b9f953a",
  secret="3cef7260cfb983138644",
  cluster="us3",
  ssl=True
)
# Catalyst 9K switch hostname or IP address
HOSTNAME = "172.27.74.111"
# Catalyst 9K switch Netconf port
PORT = "830"
# Catalyst 9K switch login credentials
USERNAME = "admin"
PASSWORD = "admin"
# Interface of which status is monitored
INTERFACE_NAME = "GigabitEthernet0/0"
#MYSQL Database Configuration
#dbconfig = {"database": "cat9", "user": "root", "password": "password","host": "localhost"}
dbconfig = {"database": "cat9", "user": "root", "password": "password","host": "host.docker.internal"}
#Iniialize connection to database
mydb = mysql.connector.pooling.MySQLConnectionPool(pool_name = "mypool", pool_size = 10, buffered=True, pool_reset_session=True, **dbconfig)
#Global list that will store raw data obtained from netconf
filter_data = []
#Global list that stores all of the device objects
device_inventory = []
#state class - used to store state data in a logical way
class state():
    def __init__(self):
      self.time_sec = 0
      self.time_usec = 0
      self.port_state = ""
      self.port_event = ""
      self.port_voltage = 0
      self.port_priority = ""
      self.cisco_pd = ""
      self.conn_chk = ""
      self.pair_pcut = ""
      self.signal_consumed_power = 0
      self.signal_pcut_icut = 0
      self.signal_capacitance = 0
      self.signal_resistance = 0
      self.signal_detect_status = 0
      self.signal_class = ""
      self.signal_assigned_class = ""
      self.spare_consumed_power = 0
      self.spare_pcut_icut = 0
      self.spare_capacitance = 0
      self.spare_resistance = 0
      self.spare_detect_status = 0
      self.spare_class = ""
      self.spare_assigned_class = ""
      self.index = 0
#port class - used to store port data in a logical way
#contains a list which stores the last 20 state objects
class port:
    def __init__(self):
        self.intf_name = ""
        self.slot = 0
        self.port_number = 0
        self.poe_intf_enabled = ""
        self.power_allocated = 0.0
        self.pd_class = ""
        self.oper_state = ""
        self.admin_state = ""
        self.oper_power = 0.0
        self.admin_police = ""
        self.oper_police = ""
        self.cutoff_power_police = 0.0
        self.module = 0
        self.oper_status = ""
        self.device_detected = ""
        self.device_name = ""
        self.discovery = ""
        self.police_state_on = ""
        self.power_admin_max = 0.0
        self.power_from_pse = 0.0
        self.power_to_pd = 0.0
        self.power_consumption = 0.0
        self.max_power_drawn = 0.0
        self.power_negotiation_used = ""
        self.lldp_tx_power_type = ""
        self.lldp_tx_power_source = ""
        self.lldp_tx_power_priority = ""
        self.lldp_tx_power_requested = 0.0
        self.lldp_tx_power_allocated = 0.0
        self.lldp_rx_power_type = ""
        self.lldp_rx_power_source = ""
        self.lldp_rx_power_priority = ""
        self.lldp_rx_power_requested = 0.0
        self.lldp_rx_power_allocated = 0.0
        self.four_pair_poe_supported = ""
        self.four_pair_poe_enabled = ""
        self.four_pair_pd_arch = ""
        self.over_current_counter = 0
        self.short_current_counter = 0
        self.initialization = ""
        self.ilp_supported = ""
        self.ilp_enabled = ""
        self.post = ""
        self.power_on = ""
        self.power_denied = ""
        self.state = ""
        self.short_circuit_detected = 0
        self.spare_pair_mode = ""
        self.spare_pair_power_is_on = ""
        self.pd_power_state = ""
        self.current_index = 0
        self.last20 = []
        self.current_state = ""
#generic device class which stores from common fields
class device:
    def __init__(self):
        self.hw_type = ""
        self.hw_dev_index = ""
        self.version  = ""
        self.part_number = ""
        self.serial_number = ""
        self.hw_description = ""
        self.dev_name = ""
        self.field_replaceable = ""
        self.hw_class = ""
        self.run_time = ""
#pim device class which extends device class
#contains a list of port objects
class pim_device(device):
    def __init__(self):
        device.__init__(self)
        self.temp_outlet = 0.0
        self.temp_inlet = 0.0
        self.temp_core = ""
        self.slot = 0
        self.num_ports = ""
        self.list_ports = [port()] * 49       
#pim device supervisor class which extends pim device class
class pim_device_supervisor(pim_device):
    def __init__(self):
        pim_device.__init__(self)
        self.temp_core = 0.0
#pim device linecard class which extends pim device class   
class pim_device_linecard(pim_device):
    def __init__(self):
        pim_device.__init__(self)

def get_intf_state_data(host, port, user, pwd, intf):
    """Fetch state of the interface from the switch.
    Open a Netconf connection to the switch and fetch
    state of the specified interface.
    Args:
        host (str): Switch hostname or IP address.
        port (str): Switch Netconf port number.
        user (str): Switch login username.
        pwd (str) : Switch login password.
        intf (str): Interface of which state to fetch.
    Returns:
        str: The XML encoded response from the switch."""
    global filter_data
    """filter to get show power data"""          
    power_filter = '''<components xmlns="http://cisco.com/ns/yang/Cisco-IOS-XE-platform-oper">
                        <component>
                          <cname/>
                          <state>
                            <temp>
                              <temp-instant/>
                            </temp>
                          </state>
                        </component>
                      </components>'''
    """filter to get show power inline data"""
    power_inline_filter = ''' <poe-oper-data xmlns="http://cisco.com/ns/yang/Cisco-IOS-XE-poe-oper">
                                <poe-port/>
                                <poe-module/>
                                <poe-stack/>
                                <poe-switch/>
                              </poe-oper-data>'''
    """filter to get hardware oper data""" 
    version_filter = '''<device-hardware-data xmlns="http://cisco.com/ns/yang/Cisco-IOS-XE-device-hardware-oper"/>'''
    """filter to the get the state data"""
    state_filter = '''<poe-health-status xmlns="http://cisco.com/ns/yang/Cisco-IOS-XE-poe-health-status">
                        <poe-port>
                          <port-num/>
                          <count/>
                          <current-index/>
                          <port-health>
                            <index/>
                            <time-sec/>
                            <time-usec/>
                            <port-state/>
                            <port-event/>
                            <is-cisco-pd/>
                            <conn-chk/>
                            <port-priority/>
                            <port-voltage/>
                            <four-pair-pcut/>
                            <signal-pair-info/>
                            <spare-pair-info/>
                          </port-health>
                        </poe-port>
                      </poe-health-status>'''
    filter_string = "/interfaces/interface[name='" + intf + "']/state"
    """ncclient connection"""
    with manager.connect(host=host, port=port, \
                         username=user, password=pwd, \
                         allow_agent=False, look_for_keys=False, \
                         hostkey_verify=False) as m:
        """GigabitEthenet0/0"""
        intf_state_xml_og = m.get(filter=("xpath", filter_string)).data_xml
        """Show Power"""
        intf_state_xml_power = m.get(('subtree', power_filter)).data_xml
        """Show Power Inline"""
        intf_state_xml_power_inline = m.get(('subtree', power_inline_filter)).data_xml
        """Show Version"""
        intf_state_xml_version = m.get(('subtree', version_filter)).data_xml
        """Show Health"""
        intf_state_xml_health = m.get(('subtree', state_filter)).data_xml
        
        """parses data into python dictionaries and adds it to the global list of raw data"""
        filter_data.append(json.dumps(xmltodict.parse(intf_state_xml_power)).split('"'))
        filter_data.append(json.loads(json.dumps(xmltodict.parse(intf_state_xml_power_inline))))
        filter_data.append(json.loads(json.dumps(xmltodict.parse(intf_state_xml_version))))
        filter_data.append(json.loads(json.dumps(xmltodict.parse(intf_state_xml_health))))
    return

#Final list that stores only the relevant devices in order
slot_list = [pim_device()] * 10
#function that parses raw data from dictionary and stores relevant data using the structure of above-created classes
def parse_data():
    #access current time and parse into correct format
    current_time = filter_data[2]['data']['device-hardware-data']['device-hardware']['device-system-data']['current-time']
    current_time = current_time.replace("T"," ")
    current_time = current_time.replace("+00:00","")
    current_time = current_time[0:19]
    #access boot time and parse into correct format
    boot_time = filter_data[2]['data']['device-hardware-data']['device-hardware']['device-system-data']['boot-time']
    boot_time = boot_time.replace("T"," ")
    boot_time = boot_time.replace("+00:00","")
    boot_time = boot_time[0:19]
    #calculate runtime based on boot time and current time
    ct = datetime.strptime(current_time, "%Y-%m-%d %H:%M:%S")
    bt = datetime.strptime(boot_time, "%Y-%m-%d %H:%M:%S")
    run_time = ct - bt
  
    global device_inventory
    #temporary list to store port data
    temp_list = []
    #obtain number of active ports
    num_ports = len(filter_data[1]['data']['poe-oper-data']['poe-port'])
    #iterate through dictionary of active ports and initialize corresponding port objects
    for i in range(int(num_ports)):
        #append port
        temp_list.append(port())
        #obtain interface name and use to set slot number and port number values for the port object
        tstring = filter_data[1]['data']['poe-oper-data']['poe-port'][i]['intf-name']
        temp_list[i].intf_name = tstring
        tlist = list(tstring.split("/"))
        temp_list[i].port_number = int(tlist[2])
        temp_list[i].slot = int(tlist[0][15:])
        #obtain poe_intf_enabled
        temp_list[i].poe_intf_enabled = filter_data[1]['data']['poe-oper-data']['poe-port'][i]['poe-intf-enabled']
        #obtain power allocated to port
        temp_list[i].power_allocated = float(filter_data[1]['data']['poe-oper-data']['poe-port'][i]['power-used'])
        #obtain pd class
        temp_list[i].pd_class = filter_data[1]['data']['poe-oper-data']['poe-port'][i]['pd-class']
        #obtain oper state
        temp_list[i].oper_state = filter_data[1]['data']['poe-oper-data']['poe-port'][i]['oper-state']
        #obtain admin state
        temp_list[i].admin_state = filter_data[1]['data']['poe-oper-data']['poe-port'][i]['admin-state']
        #obtain power used by port
        temp_list[i].oper_power = float(filter_data[1]['data']['poe-oper-data']['poe-port'][i]['oper-power'])
        #obtain admin police
        temp_list[i].admin_police = filter_data[1]['data']['poe-oper-data']['poe-port'][i]['admin-police']
        #obtain oper police
        temp_list[i].oper_police = filter_data[1]['data']['poe-oper-data']['poe-port'][i]['oper-police']
        #obtain cutoff power police
        temp_list[i].cutoff_power_police = float(filter_data[1]['data']['poe-oper-data']['poe-port'][i]['cutoff-power-police'])
        #obtain module
        temp_list[i].module = filter_data[1]['data']['poe-oper-data']['poe-port'][i]['module']
        #ildp detail
        #obtain oper status
        temp_list[i].oper_status = filter_data[1]['data']['poe-oper-data']['poe-port'][i]['ilp-detail']['oper-status']
        #obtain device detected
        temp_list[i].device_detected = filter_data[1]['data']['poe-oper-data']['poe-port'][i]['ilp-detail']['device-detected']
        #obtain device name
        temp_list[i].device_name = filter_data[1]['data']['poe-oper-data']['poe-port'][i]['ilp-detail']['device-name']
        #obtain discovery
        temp_list[i].discovery = filter_data[1]['data']['poe-oper-data']['poe-port'][i]['ilp-detail']['discovery']
        #obtain police_state_on
        temp_list[i].police_state_on = filter_data[1]['data']['poe-oper-data']['poe-port'][i]['ilp-detail']['police-state-on']
        #obtain power admin max
        temp_list[i].power_admin_max = filter_data[1]['data']['poe-oper-data']['poe-port'][i]['ilp-detail']['power-admin-max']
        #obtain power from pse
        temp_list[i].power_from_pse = filter_data[1]['data']['poe-oper-data']['poe-port'][i]['ilp-detail']['power-from-pse']
        #obtain power to pd
        temp_list[i].power_to_pd = filter_data[1]['data']['poe-oper-data']['poe-port'][i]['ilp-detail']['power-to-pd']
        #obtain power consumption
        temp_list[i].power_consumption = filter_data[1]['data']['poe-oper-data']['poe-port'][i]['ilp-detail']['power-consumption']
        #obtain max power drawn
        temp_list[i].max_power_drawn = filter_data[1]['data']['poe-oper-data']['poe-port'][i]['ilp-detail']['max-power-drawn']
        #obtain power negotiation used
        temp_list[i].power_negotiation_used = filter_data[1]['data']['poe-oper-data']['poe-port'][i]['ilp-detail']['power-negotiation-used']
        #lldp tx power type
        temp_list[i].lldp_tx_power_type = filter_data[1]['data']['poe-oper-data']['poe-port'][i]['ilp-detail']['lldp-tx-power-type']
        #lldp tx power source
        temp_list[i].lldp_tx_power_source = filter_data[1]['data']['poe-oper-data']['poe-port'][i]['ilp-detail']['lldp-tx-power-source']
        #lldp tx power priority
        temp_list[i].lldp_tx_power_priority = filter_data[1]['data']['poe-oper-data']['poe-port'][i]['ilp-detail']['lldp-tx-power-priority']
        #lldp tx power requested
        temp_list[i].lldp_tx_power_requested = filter_data[1]['data']['poe-oper-data']['poe-port'][i]['ilp-detail']['lldp-tx-power-requested']
        #lldp tx power allocated
        temp_list[i].lldp_tx_power_allocated = filter_data[1]['data']['poe-oper-data']['poe-port'][i]['ilp-detail']['lldp-tx-power-allocated']
        #lldp rx power type
        temp_list[i].lldp_rx_power_type = filter_data[1]['data']['poe-oper-data']['poe-port'][i]['ilp-detail']['lldp-rx-power-type']
        #lldp rx power source
        temp_list[i].lldp_rx_power_source = filter_data[1]['data']['poe-oper-data']['poe-port'][i]['ilp-detail']['lldp-rx-power-source']
        #lldp rx power priority
        temp_list[i].lldp_rx_power_priority = filter_data[1]['data']['poe-oper-data']['poe-port'][i]['ilp-detail']['lldp-rx-power-priority']
        #lldp rx power requested
        temp_list[i].lldp_rx_power_requested = filter_data[1]['data']['poe-oper-data']['poe-port'][i]['ilp-detail']['lldp-rx-power-requested']
        #lldp rx power allocated
        temp_list[i].lldp_rx_power_allocated = filter_data[1]['data']['poe-oper-data']['poe-port'][i]['ilp-detail']['lldp-rx-power-allocated']
        #four pair poe supported
        temp_list[i].four_pair_poe_supported = filter_data[1]['data']['poe-oper-data']['poe-port'][i]['ilp-detail']['four-pair-poe-supported']
        #four pair poe enabled
        temp_list[i].four_pair_poe_enabled = filter_data[1]['data']['poe-oper-data']['poe-port'][i]['ilp-detail']['four-pair-poe-enabled']
        #four pair pd arch
        temp_list[i].four_pair_pd_arch = filter_data[1]['data']['poe-oper-data']['poe-port'][i]['ilp-detail']['four-pair-pd-arch']
        #over current counter
        temp_list[i].over_current_counter = filter_data[1]['data']['poe-oper-data']['poe-port'][i]['ilp-detail']['over-current-counter']
        #short current counter
        temp_list[i].short_current_counter = filter_data[1]['data']['poe-oper-data']['poe-port'][i]['ilp-detail']['short-current-counter']
        #port-poe-detail
        #initialization
        temp_list[i].initialization = filter_data[1]['data']['poe-oper-data']['poe-port'][i]['port-poe-detail']['initialization']
        #ilp_supported
        temp_list[i].ilp_supported = filter_data[1]['data']['poe-oper-data']['poe-port'][i]['port-poe-detail']['ilp-supported']
        #ilp_enabled
        temp_list[i].ilp_enabled = filter_data[1]['data']['poe-oper-data']['poe-port'][i]['port-poe-detail']['ilp-enabled']
        #post
        temp_list[i].post = filter_data[1]['data']['poe-oper-data']['poe-port'][i]['port-poe-detail']['post']
        #find out if device is powered
        temp_list[i].power_on = filter_data[1]['data']['poe-oper-data']['poe-port'][i]['port-poe-detail']['power-on']
        #power denied
        temp_list[i].power_denied = filter_data[1]['data']['poe-oper-data']['poe-port'][i]['port-poe-detail']['power-denied']
        #state
        temp_list[i].state = filter_data[1]['data']['poe-oper-data']['poe-port'][i]['port-poe-detail']['state']
        #short circuit detected
        temp_list[i].short_circuit_detected = filter_data[1]['data']['poe-oper-data']['poe-port'][i]['port-poe-detail']['short-circuit-detected']
        #spare pair mode
        temp_list[i].spare_pair_mode = filter_data[1]['data']['poe-oper-data']['poe-port'][i]['port-poe-detail']['spare-pair-mode']
        #spare pair power is on
        temp_list[i].spare_pair_power_is_on = filter_data[1]['data']['poe-oper-data']['poe-port'][i]['port-poe-detail']['spare-pair-power-is-on']
        #pd power state
        temp_list[i].pd_power_state = filter_data[1]['data']['poe-oper-data']['poe-port'][i]['port-poe-detail']['pd-power-state']

        #find out the index of the current state of the poe state machine
        temp_list[i].current_index = filter_data[3]['data']['poe-health-status']['poe-port'][temp_list[i].port_number-1]['current-index']
        #iterate through the last 20 states and store data
        if (temp_list[i].slot == 1):
          for k in range(20):
            #append state object to state list
            temp_list[i].last20.append(state())
            #index of state
            temp_list[i].last20[k].index = filter_data[3]['data']['poe-health-status']['poe-port'][temp_list[i].port_number-1]['port-health'][k]['index']
            #name of state
            temp_list[i].last20[k].port_state = filter_data[3]['data']['poe-health-status']['poe-port'][temp_list[i].port_number-1]['port-health'][k]['port-state']
            #time_sec of state
            temp_list[i].last20[k].time_sec = datetime.fromtimestamp(int(filter_data[3]['data']['poe-health-status']['poe-port'][temp_list[i].port_number-1]['port-health'][k]['time-sec'])).strftime("%Y-%m-%d %H:%M:%S")
            #time_usec of state
            temp_list[i].last20[k].time_usec = datetime.fromtimestamp(int(filter_data[3]['data']['poe-health-status']['poe-port'][temp_list[i].port_number-1]['port-health'][k]['time-usec'])).strftime("%Y-%m-%d %H:%M:%S")
            #port event which triggered the current state
            temp_list[i].last20[k].port_event = filter_data[3]['data']['poe-health-status']['poe-port'][temp_list[i].port_number-1]['port-health'][k]['port-event']
            #port voltage
            temp_list[i].last20[k].port_voltage = filter_data[3]['data']['poe-health-status']['poe-port'][temp_list[i].port_number-1]['port-health'][k]['port-voltage']
            #port priority
            temp_list[i].last20[k].port_priority = filter_data[3]['data']['poe-health-status']['poe-port'][temp_list[i].port_number-1]['port-health'][k]['port-priority']
            #is cisco pd
            temp_list[i].last20[k].cisco_pd = filter_data[3]['data']['poe-health-status']['poe-port'][temp_list[i].port_number-1]['port-health'][k]['is-cisco-pd']
            #connection check
            temp_list[i].last20[k].conn_chk = filter_data[3]['data']['poe-health-status']['poe-port'][temp_list[i].port_number-1]['port-health'][k]['conn-chk']
            #4 pair pcut
            temp_list[i].last20[k].pair_pcut = filter_data[3]['data']['poe-health-status']['poe-port'][temp_list[i].port_number-1]['port-health'][k]['four-pair-pcut']
            #signal pair data readings
            #signal consumed power
            temp_list[i].last20[k].signal_consumed_power = int(filter_data[3]['data']['poe-health-status']['poe-port'][temp_list[i].port_number-1]['port-health'][k]['signal-pair-info']['consumed-power'])
            #signal pcut icut
            temp_list[i].last20[k].signal_pcut_icut = int(filter_data[3]['data']['poe-health-status']['poe-port'][temp_list[i].port_number-1]['port-health'][k]['signal-pair-info']['pcut-icut'])
            #signal capacitance
            temp_list[i].last20[k].signal_capacitance = filter_data[3]['data']['poe-health-status']['poe-port'][temp_list[i].port_number-1]['port-health'][k]['signal-pair-info']['capacitance']
            #signal resistance
            temp_list[i].last20[k].signal_resistance = filter_data[3]['data']['poe-health-status']['poe-port'][temp_list[i].port_number-1]['port-health'][k]['signal-pair-info']['resistance']
            #signal detect status
            temp_list[i].last20[k].signal_detect_status = filter_data[3]['data']['poe-health-status']['poe-port'][temp_list[i].port_number-1]['port-health'][k]['signal-pair-info']['detect-status']
            #signal class
            temp_list[i].last20[k].signal_class = filter_data[3]['data']['poe-health-status']['poe-port'][temp_list[i].port_number-1]['port-health'][k]['signal-pair-info']['class']
            #signal assigned class
            temp_list[i].last20[k].signal_assigned_class = filter_data[3]['data']['poe-health-status']['poe-port'][temp_list[i].port_number-1]['port-health'][k]['signal-pair-info']['assigned-class']
            #spare pair data readings
            #spare power
            temp_list[i].last20[k].spare_consumed_power = int(filter_data[3]['data']['poe-health-status']['poe-port'][temp_list[i].port_number-1]['port-health'][k]['spare-pair-info']['consumed-power'])
            #spare pcut icut
            temp_list[i].last20[k].spare_pcut_icut = int(filter_data[3]['data']['poe-health-status']['poe-port'][temp_list[i].port_number-1]['port-health'][k]['spare-pair-info']['pcut-icut'])
            #spare capacitance
            temp_list[i].last20[k].spare_capacitance = filter_data[3]['data']['poe-health-status']['poe-port'][temp_list[i].port_number-1]['port-health'][k]['spare-pair-info']['capacitance']
            #spare resistance
            temp_list[i].last20[k].spare_resistance = filter_data[3]['data']['poe-health-status']['poe-port'][temp_list[i].port_number-1]['port-health'][k]['spare-pair-info']['resistance']
            #spare detect status
            temp_list[i].last20[k].spare_detect_status = filter_data[3]['data']['poe-health-status']['poe-port'][temp_list[i].port_number-1]['port-health'][k]['spare-pair-info']['detect-status']
            #spare class
            temp_list[i].last20[k].spare_class = filter_data[3]['data']['poe-health-status']['poe-port'][temp_list[i].port_number-1]['port-health'][k]['spare-pair-info']['class']
            #spare assigned class
            temp_list[i].last20[k].spare_assigned_class = filter_data[3]['data']['poe-health-status']['poe-port'][temp_list[i].port_number-1]['port-health'][k]['spare-pair-info']['assigned-class']
    #find out number of devices (slots)
    num_devices = len(filter_data[2]['data']['device-hardware-data']['device-hardware']['device-inventory'])
    #iterate through slots and devices to collect relevant data
    for i in range(int(num_devices)):
        #add the right type of device
        if (filter_data[2]['data']['device-hardware-data']['device-hardware']['device-inventory'][i]['hw-type'] == "hw-type-pim"):
            if (filter_data[2]['data']['device-hardware-data']['device-hardware']['device-inventory'][i]['dev-name'].find("Supervisor") > 0):
                device_inventory.append(pim_device_supervisor())
            else:
                device_inventory.append(pim_device_linecard())
        else:
            device_inventory.append(device())
        #collect and store and common data
        #device hw type
        device_inventory[i].hw_type = filter_data[2]['data']['device-hardware-data']['device-hardware']['device-inventory'][i]['hw-type']
        #device hw dev index
        device_inventory[i].hw_dev_index = filter_data[2]['data']['device-hardware-data']['device-hardware']['device-inventory'][i]['hw-dev-index']
        #device version
        device_inventory[i].version = filter_data[2]['data']['device-hardware-data']['device-hardware']['device-inventory'][i]['version']
        #device part number
        device_inventory[i].part_number = filter_data[2]['data']['device-hardware-data']['device-hardware']['device-inventory'][i]['part-number']
        #device serial number
        device_inventory[i].serial_number = filter_data[2]['data']['device-hardware-data']['device-hardware']['device-inventory'][i]['serial-number']
        #device hw description
        device_inventory[i].hw_description = filter_data[2]['data']['device-hardware-data']['device-hardware']['device-inventory'][i]['hw-description']
        #device dev name
        device_inventory[i].dev_name = filter_data[2]['data']['device-hardware-data']['device-hardware']['device-inventory'][i]['dev-name']
        #device field replaceable
        device_inventory[i].field_replaceable = filter_data[2]['data']['device-hardware-data']['device-hardware']['device-inventory'][i]['field-replaceable']
        #device hw class
        device_inventory[i].hw_class = filter_data[2]['data']['device-hardware-data']['device-hardware']['device-inventory'][i]['hw-class']
        #devie run time
        device_inventory[i].run_time = str(run_time)  
        #collect and store device type specific data
        if (device_inventory[i].hw_type == "hw-type-pim"):
            #set inlet power search terms if linecard (inlet vs. Inlet)
            b = ""
            if (device_inventory[i].dev_name.find("Linecard") > 0):
                b = (device_inventory[i].dev_name + '.')[:-1]
                b = b.replace(" Linecard","")
                b = b.replace("Slot ","")
                #set the slot number of the device
                device_inventory[i].slot = int(b)
                searchString = "Slot" + b + "/Inlet"
                if (device_inventory[i].hw_description.find("24") > 0):
                    device_inventory[i].num_ports = "24"
                elif (device_inventory[i].hw_description.find("48") > 0):
                    device_inventory[i].num_ports = "48"
            #set inlet power search terms if supervisor (inlet vs. Inlet)
            else:
                b = (device_inventory[i].dev_name + '.')[:-1]
                b = b.replace(" Supervisor","")
                b = b.replace("Slot ","")
                #set the slot number of the device
                device_inventory[i].slot = int(b)
                searchString = "Slot" + b + "/inlet"
            #get inlet power
            if (filter_data[0].count(searchString) > 0):
                searchIndex = filter_data[0].index(searchString)
                device_inventory[i].temp_inlet = filter_data[0][searchIndex+8]
            #set outlet power search terms if linecard (outlet vs. Outlet)
            if (device_inventory[i].dev_name.find("Linecard") > 0):
                searchString = "Slot" + b + "/Outlet"
                #copy corresponding active ports from temp-list to the device inventory
                for j in temp_list[:]:
                    if (j.slot == int(device_inventory[i].dev_name[5])):
                        device_inventory[i].list_ports[j.port_number] = copy.deepcopy(j)
                        temp_list.remove(j)
            #set outlet power search terms if supervisor (outlet vs. Outlet)
            else:
                searchString = "Slot" + b + "/outlet"
            #get outlet power
            if (filter_data[0].count(searchString) > 0):
                searchIndex = filter_data[0].index(searchString)
                device_inventory[i].temp_outlet = filter_data[0][searchIndex+8]
            #get core temperature if its a supervisor
            if (device_inventory[i].dev_name.find("Supervisor") > 0):
                searchString = "Slot" + b + "/Coretemp"
                if (filter_data[0].count(searchString) > 0):
                    searchIndex = filter_data[0].index(searchString)
                    device_inventory[i].temp_core = filter_data[0][searchIndex+8]
    return

#push poe readings data to database
def sql_import():
    #initialize the connection
    conn1 = mydb.get_connection()
    #initialize the cursor
    mycursor1 = conn1.cursor()
    #set the packet size
    mycursor1.execute('set global max_allowed_packet=67108864')
    #get current time and date
    now = datetime.now()
    formatted_date = now.strftime('%Y-%m-%d %H:%M:%S')
    #push readings from device inventory to database
    for i in device_inventory:
        if(i.hw_type == "hw-type-pim"):
            for j in i.list_ports:
                if (j.intf_name != ""):
                    sql = "INSERT INTO `poe_data` (`intf_name`, `pd_class`,`oper_state`,`slot`,`port_number`, \
                          `power_allocated`, `oper_power`, `timestamp`) \
                          VALUES (%s, %s, %s, %s, %s, %s, %s, %s)"
                    val = (j.intf_name, j.pd_class, j.oper_state, j.slot, j.port_number, j.power_allocated, j.oper_power,formatted_date)
                    mycursor1.execute(sql, val)
                    conn1.commit()
    conn1.close()
    return

#global lists of labels (y-vales) and times (x-values)
line_labels = []
ref_labels = []
times = []
#variable to keep track of highest recorded power
highest_power = 0
#function that executes all functions necessary for displaying graph
def graph_thread(port,slot,channel):
    global highest_power
    global temp_dict
    #initialize database connection for querying
    conn2 = mydb.get_connection()
    #initialize database cursor to query
    mycursor2 = conn2.cursor()
    #mysql query
    sql_select_Query = "SELECT `oper_power`, `timestamp` FROM `poe_data` WHERE `port_number` = {} AND `slot` = {} AND timestamp > date_sub(now(), interval 2 minute)".format(port,slot)
    #set packet size for query
    mycursor2.execute('set global max_allowed_packet=67108864')
    #execute actual query
    mycursor2.execute(sql_select_Query)
    #fetch all of the query results and store in list of records
    records = mycursor2.fetchall()
    #close database connections
    conn2.close()
    #clear lists which will store values to reinitialize and prevent misallocation
    line_labels.clear()
    ref_labels.clear()
    times.clear()
    #store the readings in our lists along with the times
    for i in records:
        line_labels.append(i[0])
        times.append(i[1])
        ref_labels.append(slot_list[slot-1].list_ports[port].power_allocated)
    #data for power used trace
    graph_data_main = go.Scatter(
            #x values are the times
            x = times,
            #y value is the line_labels (the power consumption readings)
            y = line_labels,
            #Name of the trace
            name  = "Power Consumption",
            #Display the data points as well as the connecting lines
            mode='lines+markers',
            #set the color and width of the line
            line=dict(color='royalblue', width=4),
            #set the size and symbol for the markers
            marker=dict(size = 10, symbol = "diamond")
        )
    #data for power allocated trace
    graph_data_ref = go.Scatter(
            #x values are the times
            x = times,
            #y values are the power allocated
            y = ref_labels,
            #Name of the trace
            name  = "Power Allocated",
            #Only display the lines, not the data points
            mode='lines',
            #set the color and width of the line
            line=dict(color='firebrick', width=4)
        )
    #determine compliance of data
    compliant = "Compliant"
    if (line_labels[len(line_labels)-1] > ref_labels[len(ref_labels)-1]):
      compliant = "Not Compliant"
    #store traces in a list
    temp_data = [graph_data_ref,graph_data_main]
    #if statement which sets new highest recorded power if it exceeds what we have stored
    if (slot_list[slot-1].list_ports[port].oper_power > highest_power):
        highest_power = slot_list[slot-1].list_ports[port].oper_power
    #dictionary to hold trace data with unique key
    data = {}
    #generate unique key
    key = "graph" + str(slot) + "_" + str(port) + "_data"
    #store the trace data with the unique key in the dictionary
    data.update({ key: json.dumps((temp_data) , cls=plotly.utils.PlotlyJSONEncoder)})
    #store other data for table in lists
    #list for poe overall data
    poe_overall_data = [slot_list[slot-1].list_ports[port].poe_intf_enabled, slot_list[slot-1].list_ports[port].power_allocated, \
         slot_list[slot-1].list_ports[port].pd_class, slot_list[slot-1].list_ports[port].oper_state, \
         slot_list[slot-1].list_ports[port].admin_state, slot_list[slot-1].list_ports[port].oper_power, \
         slot_list[slot-1].list_ports[port].admin_police, slot_list[slot-1].list_ports[port].oper_police, \
         slot_list[slot-1].list_ports[port].cutoff_power_police, slot_list[slot-1].list_ports[port].module, \
         slot_list[slot-1].list_ports[port].intf_name]
    #list for other poe overall data
    poe_overall_data_other = [highest_power, str(times[len(times)-1])[0:10], str(times[len(times)-1])[11:], compliant]
    #list for lldp overall data
    poe_lldp_overall_data = [slot_list[slot-1].list_ports[port].oper_status, slot_list[slot-1].list_ports[port].device_detected, \
         slot_list[slot-1].list_ports[port].device_name, slot_list[slot-1].list_ports[port].discovery, \
         slot_list[slot-1].list_ports[port].police_state_on, slot_list[slot-1].list_ports[port].power_admin_max, \
         slot_list[slot-1].list_ports[port].power_from_pse, slot_list[slot-1].list_ports[port].power_to_pd, \
         slot_list[slot-1].list_ports[port].power_consumption, slot_list[slot-1].list_ports[port].max_power_drawn, \
         slot_list[slot-1].list_ports[port].power_negotiation_used]
    #list for lldp tx data
    poe_lldp_tx_data = [slot_list[slot-1].list_ports[port].lldp_tx_power_type, slot_list[slot-1].list_ports[port].lldp_tx_power_source, \
         slot_list[slot-1].list_ports[port].lldp_tx_power_priority, slot_list[slot-1].list_ports[port].lldp_tx_power_requested, \
         slot_list[slot-1].list_ports[port].lldp_tx_power_allocated]
    #list for lldp rx data
    poe_lldp_rx_data = [slot_list[slot-1].list_ports[port].lldp_rx_power_type, slot_list[slot-1].list_ports[port].lldp_rx_power_source, \
         slot_list[slot-1].list_ports[port].lldp_rx_power_priority, slot_list[slot-1].list_ports[port].lldp_rx_power_requested, \
         slot_list[slot-1].list_ports[port].lldp_rx_power_allocated]
    #list for lldp other data
    poe_lldp_other_data = [slot_list[slot-1].list_ports[port].four_pair_poe_supported, slot_list[slot-1].list_ports[port].four_pair_poe_enabled, \
         slot_list[slot-1].list_ports[port].four_pair_pd_arch, slot_list[slot-1].list_ports[port].over_current_counter, \
         slot_list[slot-1].list_ports[port].short_current_counter]
    #list for poe detail data
    poe_detail_data = [slot_list[slot-1].list_ports[port].initialization, slot_list[slot-1].list_ports[port].ilp_supported, \
         slot_list[slot-1].list_ports[port].ilp_enabled, slot_list[slot-1].list_ports[port].post, \
         slot_list[slot-1].list_ports[port].power_on, slot_list[slot-1].list_ports[port].power_denied, \
         slot_list[slot-1].list_ports[port].state, slot_list[slot-1].list_ports[port].short_circuit_detected, \
         slot_list[slot-1].list_ports[port].spare_pair_mode, slot_list[slot-1].list_ports[port].spare_pair_power_is_on, \
         slot_list[slot-1].list_ports[port].pd_power_state]
    #store trace dictionary and table data in a final list which we will push
    final_data = [data, poe_overall_data, poe_overall_data_other, poe_lldp_overall_data, poe_lldp_tx_data, poe_lldp_rx_data, poe_lldp_other_data, poe_detail_data]
    #command that pushes relevant data on corresponding channel
    pusher.trigger(channel, "data-updated", final_data)

#data structures used to push data
data_dict = {}
signal_data = []
spare_data = []
overall_data = []
#function that executes all functions necessary for displaying state machine
def state_thread(port,slot,name):
    global data_dict
    global signal_data
    global spare_data
    global overall_data
    #clear lists to prevent data leak and misallocation
    spare_data.clear()
    signal_data.clear()
    overall_data.clear()
    x = int(slot_list[slot-1].list_ports[port].current_index)
    #store all of the overall data
    for i in range(20):
      overall_data.append([slot_list[slot-1].list_ports[port].current_index, slot_list[slot-1].list_ports[port].last20[i].port_state, \
            slot_list[slot-1].list_ports[port].last20[i].port_event, slot_list[slot-1].list_ports[port].last20[i].port_voltage, \
            slot_list[slot-1].list_ports[port].last20[i].time_sec, slot_list[slot-1].list_ports[port].last20[i].time_usec, \
            slot_list[slot-1].list_ports[port].last20[i].port_priority, slot_list[slot-1].list_ports[port].last20[i].cisco_pd, \
            slot_list[slot-1].list_ports[port].last20[i].conn_chk, slot_list[slot-1].list_ports[port].last20[i].pair_pcut])
    #store all of the signal pair data
    for i in range(20):
      signal_data.append([slot_list[slot-1].list_ports[port].last20[i].signal_consumed_power, slot_list[slot-1].list_ports[port].last20[i].signal_pcut_icut, \
                   slot_list[slot-1].list_ports[port].last20[i].signal_capacitance, slot_list[slot-1].list_ports[port].last20[i].signal_resistance, \
                   slot_list[slot-1].list_ports[port].last20[i].signal_detect_status, slot_list[slot-1].list_ports[port].last20[i].signal_class])
    #store all of the spare pair data
    for i in range(20):
      spare_data.append([slot_list[slot-1].list_ports[port].last20[i].spare_consumed_power, slot_list[slot-1].list_ports[port].last20[i].spare_pcut_icut, \
                   slot_list[slot-1].list_ports[port].last20[i].spare_capacitance, slot_list[slot-1].list_ports[port].last20[i].spare_resistance, \
                   slot_list[slot-1].list_ports[port].last20[i].spare_detect_status, slot_list[slot-1].list_ports[port].last20[i].spare_class])
    data = [overall_data,signal_data,spare_data]
    #store data in dictionary with name as key
    data_dict.update({name: data})
    #push data on corresponding channel
    pusher.trigger(name, "data-updated", data_dict)
    
#background thread which collects all raw data every 5 seconds and stores it in the python data structures and/or the mysql databse
def data_thread():
    #turns function into thread which executes every 5 seconds
    threading.Timer(5.0, data_thread).start()
    #retrieve raw data
    intf_state_xml = get_intf_state_data(HOSTNAME, PORT, USERNAME, PASSWORD, INTERFACE_NAME)
    #parse raw data
    parse_data()
    #push relevant parsed data to database
    sql_import()
    #pick relevant PIM devices from overall device inventory and store in a separate ordered slot list
    for i in device_inventory:
      if (i.hw_type == "hw-type-pim"):
          slot_list[i.slot - 1] = i

#flask route for home page
@app.route('/')
@app.route('/index')
def index():
  global slot_list
  #initial call to get process started before the thread begins
  intf_state_xml = get_intf_state_data(HOSTNAME, PORT, USERNAME, PASSWORD, INTERFACE_NAME)
  parse_data()
  #Start background data_thread which retrieves, parses, and pushes data every 5 seconds
  data_thread()
  #extract the chassis name
  b = (device_inventory[0].hw_description + '.')[:-1]
  #reduce to just the indicator of the number of slots in the chassis
  b = b.replace("Cisco Catalyst 9400 Series ","")
  b = b.replace(" Slot Chassis","")
  #convert the string for the number of slots to an integer
  a = int(b)
  #render the corresponding data in the index.html template
  return render_template('index_test.html', device=device_inventory[0].hw_description, slot = slot_list, num_slots = a)

#flask route for graph page(s)
@app.route('/<name>')
def line(name):
    #temporary name variable for modification
    tname = copy.deepcopy(name)
    #Example Name: Gigabit_Ethernet1_0_1
    #find index of the first "_" in name
    index = tname.index("_")
    #access slot # from name - index after "t" in "Ethernet" to the first underscore is the slot
    slot = int(name[15:index])
    #replace the first "_" in Gigabit_Ethernet1_0_1 with a ""
    tname = tname.replace("_","",1)
    #find next index of the "_" in name
    index = tname.index("_")
    #access port # from name - index after second "_" to end
    port = int(name[index+2:])
    #Get the name of the device which is plugged in
    dname = slot_list[slot-1].list_ports[port].device_name
    #unique pusher channel id
    channel = name + "c"
    #background scheduler
    scheduler = BackgroundScheduler()
    #start the scheduler
    scheduler.start()
    #add a job for the scheduler
    scheduler.add_job(
        #calls graph_thread function every 3 seconds
        func=graph_thread,
        #arguments for graph_thread function
        args=[port,slot,channel],
        #trigger is 3 second interval
        trigger=IntervalTrigger(seconds=3),
        #scheduler id
        id='graph_data_retrieve',
        #scheduler name
        name='Retrieve Data for Graph Page',
        #replace existing job
        replace_existing=True,
        #combine pending jobs in case of delay
        coalesce=True,
        #max active instances in queue is 5
        max_instances = 5,
        #allow for grace time if there is a misfire
        misfire_grace_time=1000)
    # Shut down the scheduler when exiting the app
    atexit.register(lambda: scheduler.shutdown())
    #dictionary data access key
    
    key = "graph" + str(slot) + "_" + str(port) + "_data"
    #render the corresponding data in the graph_page.html template
    return render_template('graph_page.html',n = dname, t = name, port = port, c = channel, k = key)
  
#flask route for state machine page(s)
@app.route('/sd/<name>')
def sd(name):
    return render_template('state_diagram.html')
