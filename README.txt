Enviroment set up under venv

bypass the powerShell security feature to run Scripts using the following 
    Set-ExecutionPolicy -Scope Process -ExecutionPolicy Bypass
    .\venv\Scripts\activate

PS C:\Users\oscar\Documents\CPSC418\Secure_device_protocol> python secure_device_protocol__SOLUTION.py reference_device.json.gz --firmware firmware_update.bin --verbose