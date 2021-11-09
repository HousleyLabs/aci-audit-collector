### Run Nexus Dashboard Collector ###

python cnae_data_collection.py -clusterName ACI-Collector -user admin -iterations 1 -APIC <APIC_IP>

Enter password when prompted

Send new ACI-Collector_<DateTime>.tar.gz file to Housley


### Notes ###
Ignore possible errors like:
... ...
  File "cnae_data_collection.py", line 462, in getVersion
    "Candid version or ova version not present in version file.")
