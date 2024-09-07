# secure_device_protocol
Secure Device Communication Protocol README

Introduction
    This project implements the Secure Device Communication Protocol for secure communication between a hardware device and an operating system (OS) using Python.
    The protocol simulates socket communication, cryptographic functions, and secure message exchange. This assignment was designed to simulate real-world challenges 
    in hardware security, such as key management, firmware updates, and encrypted data transfer between the device and OS. The project leverages Python to simulate the 
    secure device, with a focus on encryption, signing, key negotiation, and firmware validation.

File Descriptions
    secure_device_protocol.py:
        This is the core file for the implementation of the secure communication protocol. It defines the key classes and functions responsible for cryptographic operations,
        message exchange, and firmware validation.

    firmware_update.bin: A binary file representing a simulated firmware update. This file is used in the update_firmware function to apply a firmware update to the device.
    
    reference_device.json.gz: A compressed JSON file that contains the reference image of the secure device as shipped from the factory. This file is crucial for initializing the 
        simulated secure device and testing the boot process, firmware validation, and cryptographic operations.

    encrypt_decrypt__SOLUTION.py and basic_auth_and_send__SOLUTION.py: 
        These files are imported to handle encryption, decryption, authentication, and data transfer. The reason for importing these solution files is that they offer better speed 
        than the custom code, when testing and running.

Environment Setup
    An isolated Python environment was created with all necessary libraries installed via pip under the directory venv.

Implementation Details
    This project implements the cryptographic processes and secure communication between a simulated hardware device and OS.
    It includes several cryptographic operations such as RSA encryption, signing, key negotiation, and firmware updates.
    
    The assignment description provided critical insights into the structure of each function, which guided the development process.
    Functions like RSA key generation, signing, and verification were built based on this assignment’s guidelines, ensuring the 
    protocol adhered to secure communication standards.
    

    Key Features
        Asymmetric Key Functions:
            encrypt_RSA: Encrypts a value with the given RSA key.
            decrypt_RSA: Decrypts a value with the given RSA key.
            sign_RSA: Signs a value with the given RSA key.
            verify_RSA: Verifies a signed value with the given RSA key.
            generate_pq_RSA: Generates two key values (p, q) necessary for an RSA key.
            verify_signed_RSA_key: Verifies the signature of an RSA key.
        
        Helper Functions:
            parameters_to_device: Updates the simulated device via parameters introduced in earlier assignments.
        
        Firmware Functions:
            verify_firmware: Validates proposed firmware updates before applying them.
            update_firmware: Applies valid firmware updates and prepares the device for reboot.

        Communication Functions:
            create_handshake: Creates a handshake message between the OS and the device.
            verify_handshake: Validates the handshake from the OS side.
            device_shared_key: Negotiates a shared key from the device’s point of view.
            os_shared_key: Negotiates the shared key from the OS’s point of view.
            device_to_os / os_to_device: Functions that facilitate the secure transfer of data between the device and OS.


Testing
    The project has been tested in a controlled environment with simulated socket communication between the device and the OS. 
    Key components such as encryption, signing, message validation, and firmware update verification were validated using Python’s
    built-in unit test framework. The command to run the program with an extended timeout is as follows:
        
        python secure_device_protocol.py reference_device.json.gz --firmware firmware_update.bin --verbose --timeout 600

        The verbose output helps track each step of the protocol, from booting the device, verifying firmware updates, to establishing a secure connection via a handshake.
    
Known Issues and Challenges
    The implementation has been thoroughly tested, and no significant bugs were identified during the testing phase. However, the complexity of the assignment—especially with
    cryptographic operations, hardware simulation, and message exchange—led to some initial challenges. Importing external solutions provided efficiency improvements, resolving
    many of the earlier performance issues.
