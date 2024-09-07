#!/usr/bin/env python3
"""
Template and Set Up was provided by the TA of CPSC 418, 

"""
##### IMPORTS

from __future__ import annotations

import argparse
from dataclasses import dataclass
import gzip
import json
from pathlib import Path
import socket
from sys import exit
from tempfile import TemporaryDirectory
from threading import Thread
from time import sleep, time
from typing import Any, Callable, Iterator, Mapping, Optional, Union


from os import urandom

# these functions carry over from the prior assignments
from encrypt_decrypt__SOLUTION import xor, left_encode, pseudoCSHAKE256
from encrypt_decrypt__SOLUTION import MAC_then_encrypt, decrypt_and_verify
from basic_auth_and_send__SOLUTION import ClientParameters, FastCSPRNG, PrimeChecker, ServerParameters
from basic_auth_and_send__SOLUTION import split_ip_port, int_to_bytes, bytes_to_int, i2b, b2i
from basic_auth_and_send__SOLUTION import create_socket, send, receive, receive_message, calc_k
from basic_auth_and_send__SOLUTION import create_message, verify_message, safe_prime, prim_root
from basic_auth_and_send__SOLUTION import client_handshake, client_register, server_register
from basic_auth_and_send__SOLUTION import client_key, server_key, client_file, server_file

"""
from Crypto.Cipher import AES
from hashlib import scrypt
from os import urandom
import numpy as np
from sympy import isprime

"""

class SecureDevice:
    """
    A low-level representation of the secure device we're modeling in this assignment.
      This allows us to operate as if we were a real hardware device, and yet have full
      access to Python and other things only present on a general-purpose computer.
      It also makes it easier for the auto-grader to log memory changes.
    """


    def __init__(self, bounds:list[int]=[256 << 10, 1024, 2 << 20, 10 << 20], \
            key_reserve:int=2048, state:Optional[bytes]=None):
        """
        Build the memory model of a SecureDevice. Optionally takes in the size of each 
          of four memory pools (see the assignment for details), the maximum length
          for a large variable, and an initial state.
        """

        assert len(bounds) == 4     # only four memory pools
        for size in bounds:
            assert size > 0         # all memory pools must contain bytes

        offsets = [0] * 5
        for i,size in enumerate(bounds):
            offsets[i+1] = offsets[i] + size

        assert (state is None) or (len(state) == offsets[-1])   # if given, the state must cover all memory

        # store our key boundaries
        self._lock_boot_ROM, self._RNG_start, self._FRM_start, self._RAM_start = offsets[:-1]
        self._key_reserve = key_reserve

        # set up mapped memory and the read/write masks
        self._memory = state if state else bytes( offsets[-1] )
        self._write_mask = bytes( self._RAM_start ) + bytes( [0xff]*(len(self._memory)-self._RAM_start) )
        assert len(self._write_mask) == len(self._memory)       # the write mask and memory must be the same size
        self._set_read_mask()


    def _set_read_mask(self):
        """
        An internal helper to build the read mask.
        """
        bounds = [0, self._lock_boot_ROM, self._RNG_start, self._FRM_start, len(self._memory)]
        self._read_mask = b''.join( bytes( [0xff if (i & 1) else 0] * (limit - bounds[i]) ) for i,limit in enumerate(bounds[1:]) )
        assert len(self._read_mask) == len(self._memory)       # the read mask and memory must be the same size


    def lock_ROM(self):
        """
        Lock part of the boot ROM from being read. Cannot be undone, but always unlocked
          on boot.
        """
        self._lock_boot_ROM = 4*self._key_reserve
        self._set_read_mask()

    def read(self, start:int, size:int) -> bytes:
        """
        Read a section of memory. As per the specs, areas that will always read zero are 
          respected, even if non-zero values were present in memory. Much like real-life 
          reads, reading past the end of valid memory is possible but undefined.
        """
        assert start >= 0           # only positive or zero addresses allowed
        assert size > 0             # must read at least one byte

        end = min( start + size, len(self._memory) )
        temp = bytes( [self._memory[i] & self._read_mask[i] for i in range(start,end)] )
        return temp + bytes(size - len(temp))

    def write(self, start:int, values:Union[bytes,bytearray]):
        """
        Write to a section of memory. Much like real-life memory writes, you get no 
          feedback on whether or not you succeeded.
        """
        assert start >= 0                           # only positive or zero addresses allowed
        assert type(values) in [bytes,bytearray]    # only bytes or bytearrays allowed
        assert len(values) > 0                      # must write at least one byte

        values = values[:len(self._memory) - start]     # clip to ensure a valid memory range
        if len(values) == 0:                            # early exit from a corner case
            return
        end = start + len(values)

        middle = bytes( [(v & self._write_mask[start+i]) | (self._memory[start+i] & ~self._write_mask[start+i]) for i,v in enumerate(values)] )
        self._memory = self._memory[:start] + middle + self._memory[end:]

    def memcpy(self, source:int, target:int, size:int):
        """
        A convenience function that combines a read with a write. The source and
          target cannot overlap one another.
        """
        assert source >= 0              # only positive or zero addresses allowed
        assert target >= 0              # only positive or zero addresses allowed
        assert ((source + size) < target) or ((target + size) < source)     # the two ranges cannot overlap

        self.write( target, self.read(source, size) )

    def __getitem__(self, address: int):
        """
        Read a single memory address, returning the integer value stored at that
          location if it's readable or zero otherwise.
        """
        assert address >= 0     # only positive or zero addresses allowed

        if address >= len(self._memory):
            return 0
        return self._memory[address] & self._read_mask[address]

    def __setitem__(self, address: int, value: int):
        """
        Write an integer to a single memory address, if possible. To be consistent 
          with write(), no feedback is given for invalid addresses.
        """
        assert address >= 0         # only positive or zero addresses allowed
        assert 256 > value >= 0     # the value to write must be byte sized  

        # skip no-ops
        if (address >= len(self._memory)) or (self._write_mask[address] == 0):
            return

        old_size = len(self._memory)            # to ensure we're self-consistent

        # figure out the actual value to write, then write it
        mask = self._write_mask[address]
        actual = (value & mask) | (self._memory[address] & (~mask))
        self._memory = self._memory[:address] + bytes( [actual] ) + self._memory[address+1:]

        assert len(self._memory) == old_size            # ensure the memory hasn't changed size
        assert self._memory[address] == actual          # ensure we actually wrote the value we expected

    def get_random(self):
        """
        Iterate the internal CSPRNG, returning a sequence of 16 bytes.
        """
        # exercise: what advantage does this have over the method shown in FastCSPRNG?
        retVal = pseudoCSHAKE256( self._memory[self._RNG_start:self._RNG_start + 48], 256, S=b'CPSC418 W2024 A3 CSPRNG' )
        self._memory = self._memory[:self._RNG_start+32] + retVal[:16] + self._memory[self._RNG_start+48:]
        return retVal[16:]

    def read_firmware(self):
        """
        A helper function that returns the current firmware stored on the device. Has
          the same return value as read().
        """
        return self.read( self._FRM_start, self._RAM_start - self._FRM_start )

    def write_firmware(self, address:int):
        """
        Overwrite the current firmware on the device by reading memory from the given
          :address, which must be in RAM. 
        """
        assert address >= self._RAM_start           # ensure the address really is in RAM
        values = self.read( address, self._RAM_start - self._FRM_start )        # do this manually to bypass the flags
        self._memory = self._memory[:self._FRM_start] + bytes(values) + self._memory[self._RAM_start:]

    def zero_RAM(self):
        """
        A helper function to zero out all RAM on your behalf.
        """
        self.write( self._RAM_start, bytes(self.address_size - self._RAM_start) )

    def hard_reset(self):
        """
        Signal a hard reset. As a side-effect, unlock the boot ROM.
        """
        self._lock_boot_ROM = 0
        self._set_read_mask()

    def jump_to_decrypted_code(self):
        """
        Signal that the first stage of booting is done, and we should jump to the decrypted
          code to handle the rest and enter the main loop. Should be called by your code, 
          even though it does nothing.
        """
        pass


    @property
    def address_size(self) -> int:
        """
        Returns the total number of bytes of addressable memory.
        """
        return len(self._memory)

    @property
    def device_d_RSA_addr(self) -> int:
        """
        Returns the memory address of the device's private key (d).
          Remember, this is the byte encoded version!
        """
        return 32

    @property
    def firmware_N_RSA_addr(self) -> int:
        """
        Returns the memory address of the N part of the firmware RSA key.
          Remember, this is the byte encoded version!
        """
        return self.device_d_RSA_addr + self._key_reserve

    @property
    def firmware_e_RSA_addr(self) -> int:
        """
        Returns the memory address of the e part of the firmware RSA key.
          Remember, this is the byte encoded version!
        """
        return self.firmware_N_RSA_addr + self._key_reserve

    @property
    def device_e_RSA_addr(self) -> int:
        """
        Returns the memory address of e from the device's public key.
          Remember, this is the byte encoded version!
        """
        return self._RNG_start - self._key_reserve

    @property
    def device_N_RSA_addr(self) -> int:
        """
        Returns the memory address of N from the device's public key.
          Remember, this is the byte encoded version!
        """
        return self.device_e_RSA_addr - self._key_reserve

    @property
    def device_RSA_signature_addr(self) -> int:
        """
        Returns the memory address of the device public key signature,
          made by the original model key. Remember, this is the byte 
          encoded version!
        """
        return self.device_N_RSA_addr - self._key_reserve

    @property
    def model_key_tag_addr(self) -> int:
        """
        Returns the memory address of the tag of the model key used to
          sign the device key. Remember, this is the byte encoded version!
        """
        return self.device_RSA_signature_addr - self._key_reserve

    @property
    def model_key_bits_addr(self) -> int:
        """
        Returns the memory address of the size of the model key used to
          sign the device's public key. Remember, this is the byte 
          encoded version!
        """
        return self.model_key_tag_addr - 4

    @property
    def device_salt_addr(self) -> int:
        """
        Returns the memory address of device's private salt.
          Remember, this is the byte encoded version!
        """
        return self.model_key_bits_addr - self._key_reserve

    @property
    def firmware_nonce_addr(self) -> int:
        """
        Returns the memory address of nonce used to obfuscate the encrypted 
          firmware.
        """
        return self._FRM_start

    @property
    def obfuscated_firmware_addr(self) -> int:
        """
        Returns the memory address of the obfuscated encrypted firmware.
        """
        return self.firmware_nonce_addr + 32


    @property
    def N_DH_addr(self) -> int:
        """
        Returns the memory address of the device's current N that's used for
          Diffie-Hellman. Remember, this is the byte encoded version!
        """
        return self._RAM_start

    @property
    def g_DH_addr(self) -> int:
        """
        Returns the memory address of the device's current g that's used for
          Diffie-Hellman. Remember, this is the byte encoded version!
        """
        return self.N_DH_addr + self._key_reserve

    @property
    def key_DH_addr(self) -> int:
        """
        Returns the memory address of the negotiated session key, reached via 
          Diffie-Hellman. Remember, this is the byte encoded version!
        """
        return self.g_DH_addr + self._key_reserve

    @property
    def message_count_addr(self) -> int:
        """
        Returns the memory address of the current session's message count.
          Remember, this is the byte encoded version!
        """
        return self.key_DH_addr + self._key_reserve

    @property
    def s_DH_addr(self) -> int:
        """
        Returns the memory address of the salt value used during session key
          negotiation. Remember, this is the byte encoded version!
        """
        return self.message_count_addr + 8

    @property
    def v_DH_addr(self) -> int:
        """
        Returns the memory address of the value of v used during session key
          negotiation. Remember, this is the byte encoded version!
        """
        return self.s_DH_addr + self._key_reserve

    @property
    def p_DH_addr(self) -> int:
        """
        Returns the memory address of the value of p used during session key
          negotiation. Remember, this is the byte encoded version!
        """
        return self.v_DH_addr + self._key_reserve

    @property
    def k_DH_addr(self) -> int:
        """
        Returns the memory address of the value of k used during session key
          negotiation. Remember, this is the byte encoded version!
        """
        return self.p_DH_addr + self._key_reserve

    @property
    def A_DH_addr(self) -> int:
        """
        Returns the memory address of the value of A used during session key
          negotiation. Remember, this is the byte encoded version!
        """
        return self.k_DH_addr + self._key_reserve

    @property
    def b_DH_addr(self) -> int:
        """
        Returns the memory address of the value of b used during session key
          negotiation. Remember, this is the byte encoded version!
        """
        return self.A_DH_addr + self._key_reserve

    @property
    def B_DH_addr(self) -> int:
        """
        Returns the memory address of the value of B used during session key
          negotiation. Remember, this is the byte encoded version!
        """
        return self.b_DH_addr + self._key_reserve

    @property
    def u_DH_addr(self) -> int:
        """
        Returns the memory address of the value of u used during session key
          negotiation. Remember, this is the byte encoded version!
        """
        return self.B_DH_addr + self._key_reserve

    @property
    def Y_DH_addr(self) -> int:
        """
        Returns the memory address of the value of Y used during session key
          negotiation. Remember, this is the byte encoded version!
        """
        return self.u_DH_addr + self._key_reserve

    @property
    def M1_DH_addr(self) -> int:
        """
        Returns the memory address of the value of M1 used during session key
          negotiation. Remember, this is the byte encoded version!
        """
        return self.Y_DH_addr + self._key_reserve

    @property
    def ephemeral_p_RSA_addr(self) -> int:
        """
        Returns the memory address of the ephemeral RSA key's value of p.
          Remember, this is the byte encoded version!
        """
        return self.M1_DH_addr + self._key_reserve

    @property
    def ephemeral_q_RSA_addr(self) -> int:
        """
        Returns the memory address of the ephemeral RSA key's value of q.
          Remember, this is the byte encoded version!
        """
        return self.ephemeral_p_RSA_addr + (self._key_reserve >> 1)

    @property
    def ephemeral_e_RSA_addr(self) -> int:
        """
        Returns the memory address of the ephemeral RSA key's value of e.
          Remember, this is the byte encoded version!
        """
        return self.ephemeral_q_RSA_addr + (self._key_reserve >> 1)

    @property
    def ephemeral_d_RSA_addr(self) -> int:
        """
        Returns the memory address of the ephemeral RSA key's value of d.
          Remember, this is the byte encoded version!
        """
        return self.ephemeral_e_RSA_addr + self._key_reserve

    @property
    def decrypted_firmware_tag_addr(self) -> int:
        """
        Returns the memory address used to store a tag of the decrypted
          firmware. Remember, this is the byte encoded version!
        """
        return self.ephemeral_d_RSA_addr + self._key_reserve

    @property
    def firmware_key_signature_addr(self) -> int:
        """
        Returns the memory address used to store a signature of the decrypted
          firmware tag and the ephemeral public key, signed by the device key.
          Remember, this is the byte encoded version!
        """
        return self.decrypted_firmware_tag_addr + 64     # leave room for future expansion

    @property
    def decrypted_firmware_addr(self) -> int:
        """
        Returns the memory address used to store decrypted copies of the
          firmware. This is used during runtime to reference variables
          contained within the encrypted firmware, and as temporary 
          storage when doing a firmware upgrade.
        """
        return self.address_size - (self._RAM_start - self._FRM_start)

    @property
    def downloaded_firmware_addr(self) -> int:
        """
        Returns the memory address used to temporarily store the firmware bundle
          the operating system has sent to the secure device, in anticipation
          of a firmware upgrade. See the assignment spec for details on how it
          is formatted.
        """
        return self.decrypted_firmware_addr - (self._RAM_start - self._FRM_start) - 2*self._key_reserve

    @property
    def model_N_RSA_addr(self) -> int:
        """
        Returns the memory address of the N part of the model RSA key.
          Remember, this is the byte encoded version!
        """
        return self.decrypted_firmware_addr + 32

    @property
    def model_e_RSA_addr(self) -> int:
        """
        Returns the memory address of the d part of the model RSA key.
          Remember, this is the byte encoded version!
        """
        return self.model_N_RSA_addr + self._key_reserve

    @property
    def vendor_N_RSA_addr(self) -> int:
        """
        Returns the memory address of the N part of the vendor RSA key.
          Remember, this is the byte encoded version!
        """
        return self.model_e_RSA_addr + self._key_reserve

    @property
    def vendor_e_RSA_addr(self) -> int:
        """
        Returns the memory address of the d part of the vendor RSA key.
          Remember, this is the byte encoded version!
        """
        return self.vendor_N_RSA_addr + self._key_reserve

    @property
    def OS_N_RSA_addr(self) -> int:
        """
        Returns the memory address of the N part of the OS RSA key.
          Remember, this is the byte encoded version!
        """
        return self.vendor_e_RSA_addr + self._key_reserve

    @property
    def OS_e_RSA_addr(self) -> int:
        """
        Returns the memory address of the d part of the OS RSA key.
          Remember, this is the byte encoded version!
        """
        return self.OS_N_RSA_addr + self._key_reserve

    @property
    def maximum_messages_addr(self) -> int:
        """
        Returns the memory address containing the maximum number
          of messages allowed before a key should be re-negotiated.
          Remember, this is the byte encoded version!
        """
        return self.OS_e_RSA_addr + self._key_reserve

    @property
    def ephemeral_key_bits_addr(self) -> int:
        """
        Returns the memory address containing the number of bits
          to use when generating ephemeral keys.
          Remember, this is the byte encoded version!
        """
        return self.maximum_messages_addr + 8


class DeviceCSPRNG(FastCSPRNG):
    """
    Modifies FastCSPRNG to use a SecureDevice's CSPRNG instead. Handy for
      use with A2's code.
    """
    def __init__(self, device:SecureDevice):
        assert hasattr( device, 'get_random' )

        FastCSPRNG.__init__(self)
        self._device = device

    def _inc(self):             # only possible because of matching block sizes
        self._buffer += self._device.get_random()
        self._counter += 1


def encrypt_RSA( plaintext:bytes, N:bytes, e:bytes, d:Optional[bytes]=None ) -> bytes:
    """
    Encrypt a value with the given RSA key. To interface well with the rest
      of the code, all inputs and outputs are bytes objects.

    PARAMETERS
    ==========
    plaintext: The bytes object to encrypt. Note that this must be two bytes
      shorter than the byte encoding of N.
    N, e: The byte encodings of the public portion of the RSA key.
    d: The byte encoding of the private portion of the RSA key. May not be
      available, in some contexts.

    RETURNS
    =======
    The encrypted value, as a byte sequence. If a required input is
      missing, it is acceptable to throw an exception or fail an assertion.
    """
    assert type(plaintext) is bytes
    assert type(N) is bytes
    assert type(e) is bytes
    assert len(plaintext) < len(N)
    assert len(N) == len(e)
    assert (d is None) or (type(d) is bytes)

    # Extract the bit length of the RSA key
    bits = (N[0] << 8) + e[0]

    #create a bit mask that will limit the bit length of the calculation 
      # a #1 will be created for each bit in N & e
    mask = (1 << bits) - 1   

    #convert N and e from bytes --> int and apply the mask 
      #lambda function will iterate over every index of N and e and convert to them to int 
      #mask use for length integraty 

    N_rsa, e_rsa = map( lambda x: bytes_to_int( x[1:] ) & mask, [N, e] )
                                                              
    # RSA encryption formula: ciphertext = plaintext^e mod N
    cypher = pow( bytes_to_int(plaintext), e_rsa, N_rsa )
  
    # Convert ciphertext back to bytes, ensuring it matches the length of N.
    ciphertext = int_to_bytes(cypher, len(e) - 1)  

    return ciphertext


def decrypt_RSA( cyphertext:bytes, N:bytes, e:bytes, d:Optional[bytes]=None ) -> bytes:
    """
    Decrypt a value with the given RSA key. To interface well with the rest
      of the code, all inputs and outputs are bytes objects.

    PARAMETERS
    ==========
    cyphertext: The bytes object to decrypt. Note that this must be one
      byte shorter than the byte encoding of N.
    N, e: The byte encodings of the public portion of the RSA key.
    d: The byte encoding of the private portion of the RSA key. May not be
      available, in some contexts.

    RETURNS
    =======
    The decrypted value, as a byte sequence. If a required input is
      missing, it is acceptable to throw an exception or fail an assertion.
    """
    assert type(cyphertext) is bytes
    assert type(N) is bytes
    assert type(e) is bytes
    assert len(cyphertext) < len(N)
    assert len(N) == len(e)
    assert (d is None) or (type(d) is bytes)

    #check that d is avalible 
    assert type(d) is bytes 
    assert len(d) == len(e) - 1
     
    # Extract the bit length of the RSA key
    bits = (N[0] << 8 ) + e[0]

    #create a bit mask that will limit the bit length of the calculation 
      # a #1 will be created for each bit in N & e
    mask = (1 << bits) -1   

    #convert N and d from bytes --> int and apply the mask 
      #mask use for length integraty 
    N_rsa = bytes_to_int( N[1:] ) & mask
    d_rsa = bytes_to_int( d ) & mask
    
                                                              
    # RSA encryption formula: plaintext = cyphertext^d mod N
    plain = pow( bytes_to_int(cyphertext), d_rsa, N_rsa )
  
    # Convert ciphertext back to bytes, ensuring it matches the length of N.
    plaintxt = int_to_bytes( plain, len(e)-1 )  

    return plaintxt

def sign_RSA( value:bytes, N:bytes, e:bytes, d:Optional[bytes]=None ) -> bytes:
    """
    Sign a value with the given RSA key. To interface well with the rest
      of the code, all inputs and outputs are bytes objects.

    PARAMETERS
    ==========
    value: The bytes object to sign. Note that this must be two bytes shorter
      than the byte encoding of N.
    N, e: The byte encodings of the public portion of the RSA key.
    d: The byte encoding of the private portion of the RSA key. May not be
      available, in some contexts.

    RETURNS
    =======
    The decrypted value, as a byte sequence. If a required input is
      missing, it is acceptable to throw an exception or fail an assertion.
    """
    assert type(value) is bytes
    assert type(N) is bytes
    assert type(e) is bytes
    assert len(value) < len(N)
    assert len(N) == len(e)
    assert (d is None) or (type(d) is bytes)


    #check that d is avalible 
    assert type(d) is bytes 
    assert len(d) == len(e) - 1

    # RSA signing is mathematically the same as RSA decryption.
    # We can therefore use the decrypt_RSA function to perform signing.
    return decrypt_RSA( value, N, e, d )

def verify_RSA( signature:bytes, value:bytes, N:bytes, e:bytes, d:Optional[bytes]=None ) -> bool:
    """
    Verify a signature made with the given RSA key of a specific value. To interface 
      well with the rest of the code, all inputs are bytes objects.

    PARAMETERS
    ==========
    signature: The signature of value. Note that this must be one byte
      shorter than the byte encoding of N.
    value: The value that was signed. Note that this must be two bytes shorter
      than the byte encoding of N.
    N, e: The byte encodings of the public portion of the RSA key.
    d: The byte encoding of the private portion of the RSA key. May not be
      available, in some contexts.

    RETURNS
    =======
    True if the signature matches, False otherwise.
    """
    assert type(signature) is bytes
    assert type(value) is bytes
    assert type(N) is bytes
    assert type(e) is bytes
    assert len(signature) < len(N)
    #print(f"verify_RSA: len(value) = {len(value)}, len(N) = {len(N)}", flush=True)
    assert len(value) < len(N)
    assert len(N) == len(e)
    assert (d is None) or (type(d) is bytes)
    
    # Extract the bit length of the RSA key
    bits = (N[0] << 8) + e[0]

    #create a bit mask that will limit the bit length of the calculation 
      # a #1 will be created for each bit in N & e
    mask = (1 << bits) - 1   

    #convert N and e from bytes --> int and apply the mask 
      #lambda function will iterate over every index of N and e and convert to them to int 
      #mask use for length integraty 

    N_rsa, e_rsa = map( lambda x: bytes_to_int( x[1:] ) & mask, [N, e] )

    #perform RSA verification.
    #the RSA verification formula is value = signature^e mod N
    verify = pow(bytes_to_int(signature), e_rsa, N_rsa)
    
    #if verify matches the original value then RETURN
    return verify == bytes_to_int(value)

def generate_key_tag( signing_key:tuple[bytes], signed_key:tuple[bytes],
                          type_of_key:bytes ) -> bytes:
    """
    Generate the tag to be signed by an RSA key. To interface well with the rest of the 
      code, all inputs are bytes objects.

    PARAMETERS
    ==========
    signing_key: A tuple of the signing key's N and e values, both as bytes, in that order.
    signed_key: A tuple of the signed RSA key's N and e values, both as bytes, in that order.
    type_of_key: The byte sequence to use as a customization for the signature.

    RETURNS
    =======
    A byte sequence containing the signature.
    """
    assert type(signing_key) is tuple
    assert len(signing_key) == 2
    assert len(signing_key[0]) == len(signing_key[1])

    assert type(signed_key) is tuple
    assert len(signed_key) == 2
    assert len(signed_key[0]) == len(signed_key[1])

    assert type(type_of_key) is bytes
    assert len(type_of_key) > 0
     
    # Using CSHAKE for hashing with the type of key as customization
    """
    - "len(signing_key[0])" gives you the length of this byte sequence.
    - "- 2 " excluding the length bytes.
    - "<<3" Because we’re converting from bytes to bits (2^3 = 8).
    """

    return pseudoCSHAKE256( b''.join(signed_key), (len(signing_key[0])-2) << 3, b"PUBLIC KEY SIGNATURE", \
                            type_of_key )

def verify_signed_RSA_key( signature:bytes, signing_key:tuple[bytes], signed_key:tuple[bytes],
                          type_of_key:bytes ) -> bool:
    """
    Specialize verify_RSA to handle the signature of an RSA key. To interface well with the rest 
      of the code, all inputs are bytes objects.

    PARAMETERS
    ==========
    signature: The signature of value. Note that this must be one byte
      shorter than the byte encoding of N.
    signing_key: A tuple of the signing key's N and e values, both as bytes, in that order.
    signed_key: A tuple of the signed RSA key's N and e values, both as bytes, in that order.
    type_of_key: The byte sequence to use as a customization for the signature.

    RETURNS
    =======
    True if the signature matches, False otherwise.
    """
    assert type(signature) is bytes
    assert len(signature) < len(signing_key[0])

    assert type(signing_key) is tuple
    assert len(signing_key) == 2
    assert len(signing_key[0]) == len(signing_key[1])

    assert type(signed_key) is tuple
    assert len(signed_key) == 2
    assert len(signed_key[0]) == len(signed_key[1])

    assert type(type_of_key) is bytes
    assert len(type_of_key) > 0

    # reconstruct the value that was signed
    value = generate_key_tag( signing_key, signed_key, type_of_key )

    # then defer to the general routine
    return verify_RSA( signature, value, signing_key[0], signing_key[1] )

def generate_pq_RSA( N_bits:int, device:SecureDevice ) -> tuple[bytes]:
    """
    Generate the two values necessary to calculate N.

    PARAMETERS
    ==========
    N_bits: An integer representing the number of bits that N will have. Note that this is
      not the same as the size of p or q!
    device: The SecureDevice to draw random bytes from.

    RETURNS
    =======
    A tuple containing two byte values, representing p and q.
    """

    assert N_bits > 4
    assert (N_bits & 1) == 0            # must be even!
    assert isinstance(device, object)

    #Set up random number generator and prime checker 
    rng = FastCSPRNG(device)
    prim = PrimeChecker()
    
    

    #Determine the length of q and p 
      # RSA, p and q must produce a specific bit length (N_bits)
      # N = p * q and we want 'N_bits', p and q should each have about half the but length 
    
    # N_bits // 2 
    sub_bits = N_bits >> 1


    #generate p and q safe primes     
    p = safe_prime( sub_bits, rng, prim )
    q = safe_prime( sub_bits, rng, prim )
    
    #loop until p and q such that the product has "N_bits" and p != q
    while ( (p*q).bit_length() != N_bits ) or (p == q):
        p = safe_prime( sub_bits, rng, prim )
        q = safe_prime( sub_bits, rng, prim )
    
    #convert p and q to bytes 
    # - `byte_length`: The number of bytes required to represent a prime of `sub_bits` length, round up.

    byte_length = (sub_bits + 7) >> 3

    #return the q and p pair 
    return tuple(map( lambda x: int_to_bytes( x, byte_length ), [p,q] ))



def generate_RSA_key( p:bytes, q:bytes, device:SecureDevice ) -> tuple[bytes]:
    """
    Given suitable values of p and q, finish generating the RSA key.
      Note that you should not rely on pow() or external libraries to do your
      work; you may write and invoke helper functions, so long as they
      follow the same rules.

    PARAMETERS
    ==========
    p, q: Two byte sequences representing the two values needed to complete an 
      RSA key.
    device: The SecureDevice to draw random bytes from.

    RETURNS
    =======
    A tuple containing the binary enconding of N, e, and d, in that order, as 
      bytes objects.
    """
    assert type(p) is bytes
    assert type(q) is bytes
    assert isinstance(device, object)

    # Convert p and q from bytes to integers
    p, q = map( bytes_to_int, [p,q] )

    # Calculate N (the modulos)
    N = p * q
    N_bit_len = N.bit_length()
    N_byte_len = (N_bit_len + 7) >> 3 # converting it to byte length 

    # N byte representation by splitting it to most significant (len) and less significant (value)
    N_bytes = bytes([N_bit_len >> 8]) + int_to_bytes(N, N_byte_len)

    #Euclidean algorithm funct 
    # Euclidean (e,phi_N) : helper function to calculate the inverseof e modulo phi_N and the gcd 
    def euclidean(e, phi_N):

        """
        A helper to calculate the inverse of e modulo phi_N and the GCD via the
          extended Euclidean algorithm.
        """

        #value
        i = (1, phi_N -1)
        #remainder 
        r = (e, phi_N - e)
        
        #continue until the remainder is 0 (GCD)
        while abs(r[1]) > 0: 
            q = r[0] // r [1] #calc quotient 
            
            #extended euclidean algorithm, GDC of the 2 numbers and modular inverse.
            #apply map function to the tuple [i,r]

            # for i: (x[0] - q * x[1]) % phi_N) computes Value based on eucladian algorithm    
            # for r: (x[0] - q * x[1]) % phi_N) computes the new remainder 
            i, r = map( lambda x: (x[1], (x[0] - q*x[1]) % phi_N), [i,r] )
        
        return i[0], r[0]
    
    #calculate phi(N) (eulors totient function for N)
    #-phi is calculated as (p-1)*(q-1), generating the private exponent of d
    phi_N = (p-1)*(q-1)
    mask = (1 << N_bit_len) -1 #bit mask for security 

    #generate public exponent e
    rng = DeviceCSPRNG(device)

    #Generating e
    while True:
        #generate e within the correct length
        e = bytes_to_int( rng.get(N_byte_len) ) & mask 
        
        # e most be valid (which is > 1 and < than phi(N))
        if (e > phi_N) or (e < 2):
            continue
        
        #modular inverse of e (the private exponnent d)
        inverse, gcd = euclidean(e, phi_N)
        
        #check that e and phi(N) are coprime
        if gcd ==1: 
            break
    
    # e byte representation  
      #  N_bit_len & 0xff (8 bits set to 1) = extracting the lower 8 bits of N_bit_len
      #  single byte of the lower 8bits and e byte array of len N
      
      #  e byte = lower 8bits of 'N_bit_len' + rest of bytes of actual e 
      #  assuring that the len of N is known and e is consistent with bit length N

    e_bytes = bytes( [N_bit_len & 0xff] ) + int_to_bytes( e, N_byte_len )
    
    #d converted to byte
    d_bytes = int_to_bytes(inverse, N_byte_len)

    
    return N_bytes, e_bytes, d_bytes  



def device_to_parameters( device:SecureDevice, IP:str="127.0.4.18", port:int=3180 ) -> \
        tuple[ClientParameters,ServerParameters]:
    """
    Given a SecureDevice, create a ClientParameters and ServerParameters pair
      from the information the device contains. Useful for interfacing with
      A2's code. Note that the only valid zero value is for the message count,
      everything else either cannot be zero or the odds of it being zero are
      so small as to be negligible. The device must have fully booted.

    PARAMETERS
    ==========
    device: The SecureDevice to draw values from.
    IP: The TCP/IP address the Server listens on, as a string.
    port: The TCP/IP port number the Server listens on, as an int.

    RETURNS
    =======
    A tuple consisting of (ClientParameters, ServerParameters).
    """
    assert isinstance(device, object)
    assert type(IP) is str
    assert 0 < port < 65536

    # First, extract the number of bits for the ephemeral RSA key
    ephemeral_key_size_bits =  bytes_to_int(device.read(device.ephemeral_key_bits_addr, 4))

    #check if the device has booted (ephemeral != 0)
    if ephemeral_key_size_bits == 0:
        raise ValueError("Device not fully booted, as ephemeral key bits are zero.") 
    
    # bits --> bytes 
    ephemeral_key_size_bytes = (ephemeral_key_size_bits + 7) // 8 

    #helper function use to read values from device memory 
    def read_value_or_none(device, addr, length):
        
        #read values from the device and return None if the values is 0
        value = device.read(addr, length)
        return None if value == bytes(length) else value
    
 
    # Creating ClientParameters and populate them with the values of the device 
    server_params = ServerParameters( ((ephemeral_key_size_bits>>1) + 7) >> 3, 16, 32, IP, port )

    # read and set the message count from the device 
    server_params.message_count = bytes_to_int(device.read(device.message_count_addr, 8))

    #populate Server parameters with diffie-helman values
    for attr in ['N', 'g', 'k', 'b','B','u', 'Y', 'M1']:
        setattr(server_params, attr, read_value_or_none(device, getattr(device, f'{attr}_DH_addr'), server_params.int_bytes))

    #read and set the server's session key (K_server)
    server_params.K_server = read_value_or_none(device, device.key_DH_addr, server_params.int_bytes)


    #create the Clientparameters
    client_params = ClientParameters()

    #set the client message count to match the servers message count
    client_params.message_count = server_params.message_count

    #populate client parameters with diffie-helman values
    for attr in ['v', 'p', 'A', 'u', 'Y', 'M1']:
        setattr(client_params, attr, read_value_or_none(device, getattr(device, f'{attr}_DH_addr'), server_params.int_bytes))

    #read and set the client's salt value 
    client_params.s = read_value_or_none(device, device.s_DH_addr, server_params.salt_bytes)

    #read and set the client's session key to match the server's session key 
    client_params.K_client = server_params.K_server

    return client_params, server_params


def parameters_to_device( device:SecureDevice, cp:Optional[ClientParameters], \
        sp:Optional[ServerParameters] ):
    """
    Update a SecureDevice with information contained in the given ClientParameters 
      and ServerParameters. Useful for allowing Assignment 2's code to interface
      with Assignment 3's. Note that this operation modifies the SecureDevice
      object. Note as well the only time zero is considered valid is when dealing
      with the current message count.

    PARAMETERS
    ==========
    device: The SecureDevice to draw values from.
    cp: The ClientParameters containing values to store. Parameters containing
      None are skipped.
    sp: The ServerParameters containing values to store. Parameters containing
      None are skipped.
    """
    assert isinstance(device, object)
    assert (cp is None) or isinstance(cp, ClientParameters)
    assert (sp is None) or isinstance(sp, ServerParameters)

    #exit early if both paramaters are None (Nothing to update)
    if cp is None and sp is None:
        return 


    # get ephemeral key bit length and calculate byte length 
    ephemeral_key_bits = bytes_to_int(device.read(device.ephemeral_key_bits_addr, 4))
    ephemeral_key_bytes =(ephemeral_key_bits + 7)// 8
    int_bytes = ((ephemeral_key_bits // 2) + 7) // 8

    #write clientParameters to the device memory
    if cp is not None:
        #write client DH values to corresponding memory address
        for attr in ['v', 'p', 'A', 'u', 'Y', 'M1']:
            value = getattr(cp, attr)
            if value is not None:
                device.write(getattr(device,f'{attr}_DH_addr'),i2b(value,int_bytes))

        #write the client's salt value to the device memory 
        if cp.s is not None:
            device.write(device.s_DH_addr,i2b(cp.s, 32 if sp is None else sp.salt_bytes))    
        
        #write the client's key value to the device memory 
        if cp.K_client is not None:
            device.write(device.key_DH_addr, i2b(cp.K_client,int_bytes))                
        
        #update the message count in the device memory
        device.write(device.message_count_addr, i2b(cp.message_count, 8))

    #write ServerParameters to the device in memory 
    if sp is not None:
      for attr in ['N','g','k','b','B','u','Y','M1']:
          value = getattr(sp, attr)
          if value is not None:
              device.write(getattr(device, f'{attr}_DH_addr'), i2b(value, int_bytes))

      # Update the server's session key if not already written by the client
      if cp is None:      # save some writes

            if sp.K_server is not None:
                device.write( device.key_DH_addr, i2b( sp.K_server, int_bytes ) )
                # Update the message count in the device memory
            device.write( device.message_count_addr, i2b( sp.message_count, 8 ) )
        
    return

def verify_firmware( device:SecureDevice ) -> bool:
    """
    Verify a proposed firmware update. Note that the update itself is stored 
      in RAM, at a specific memory address. You may assume the device is 
      well past its first boot stage.

    PARAMETERS
    ==========
    device: The SecureDevice to draw values from.

    RETURNS
    =======
    True if the update was valid, False otherwise.
    """
    assert isinstance(device, object)

    #Check the magic value to ensure the update has the correct header.
      #a fixed byte string that serves as a unique identifier for the firmware.
    magic = b'CPSC418 MATH318 W2024'
    
    # Read the magic value from the beginning of the firmware stored in RAM.
    if device.read(device.downloaded_firmware_addr, len(magic)) != magic:
        # If the magic value doesn't match, the firmware is invalid.
        return False  

    #Set the initial offset for reading the firmware data just after the magic value.
    offset = device.downloaded_firmware_addr + len(magic)

    # Verify the key tags for model, vendor, and OS.
    # tags are derived from the public keys and must match expected values.
    key_sizes = dict()  
    
    for key_type in ['model', 'vendor', 'OS']:
        # Read the key tag from the firmware.
        key_tag = device.read(offset, 16)
        
        # Calculate the size of the RSA key for this key type.
        key_bits = (device[ getattr(device, f'{key_type}_N_RSA_addr') ] << 8) + \
                   device[ getattr(device, f'{key_type}_e_RSA_addr') ]
        key_bytes = (key_bits + 7) >> 3  
        
        # Store the key size for later use.
        key_sizes[key_type] = key_bits
        
        # Create a pseudo hash of the public key to compare against the key tag.
        to_tag = device.read(getattr(device, f'{key_type}_N_RSA_addr'), key_bytes + 1) + \
                 device.read(getattr(device, f'{key_type}_e_RSA_addr'), key_bytes + 1)
        
        # Verify that the key tag matches the expected hash.
        if key_tag != pseudoCSHAKE256(to_tag, 16 << 3, b'PUBLIC KEY', key_type.upper().encode('utf-8')):
            return False 
        
        # Move the offset forward to the next tag.
        offset += 16

    # Verify the firmware signature.
    # The signature is signed by the OS, vendor, and model keys in reverse order.
    # Convert OS key size from bits to bytes.
    os_key_bytes = (key_sizes['OS'] + 7) >> 3  
    
    # Read the stored signature from the firmware.
    stored_signature = device.read(offset, os_key_bytes)
    # Move the offset past the signature.
    offset += os_key_bytes  
    
    # Initialize the signed tag for decryption.
    signed_tag = stored_signature  
    
    for key_type in ['OS', 'vendor', 'model']:
        # Calculate key size and convert to bytes.
        key_bits = key_sizes[key_type]
        key_bytes = (key_bits + 7) >> 3
        
        # Convert the signed tag back to an integer.
        signed_number = bytes_to_int(signed_tag)
        
        # Ensure the signed number doesn't exceed the key size.
        if signed_number.bit_length() > key_bits:
            return False  
        
        # Convert the signed tag to the expected size in bytes.
        signed_tag = int_to_bytes(signed_number, key_bytes)
        
        # Decrypt the signed tag using the public RSA key for this key type.
        signed_tag = encrypt_RSA(signed_tag, 
                                 device.read(getattr(device, f'{key_type}_N_RSA_addr'), key_bytes + 1), 
                                 device.read(getattr(device, f'{key_type}_e_RSA_addr'), key_bytes + 1))

    # Validate the decrypted firmware tag.
    # The tag should start with a zero byte, indicating successful decryption.
    if signed_tag[0] != 0:
        return False 
    
    #Calculate the expected size of the firmware.
    firmware_size = device.N_DH_addr - device.obfuscated_firmware_addr
    
    # Generate the expected firmware tag by hashing the firmware contents.
    firmware_tag = pseudoCSHAKE256(device.read(offset, firmware_size), (len(signed_tag) - 1) << 3, 
                                   magic, b'FIRMWARE SIGNATURE')
    
    # Compare the decrypted firmware tag to the expected tag.
    # If they match, the firmware is valid.
    return signed_tag[1:] == firmware_tag

def update_firmware( device:SecureDevice ):
    """
    Perform all the steps necessary for a firmware update. You may assume
      the image has been verified. Note that the given device will be modified,
      and that wiping RAM and a hard reset must be performed.

    PARAMETERS
    ==========
    device: The SecureDevice to draw values from.
    """
    assert isinstance(device, object)

    #Backup the OS Key bits before making changes
    OS_key_bits =(device[device.OS_N_RSA_addr] << 8) + device[device.OS_e_RSA_addr]

    #Generate a 32-byte nonce for firmware obscuration 
    #nonce used to generate noise patterns that will obscure the firmware data
    nonce = device.get_random() + device.get_random()  #32 bytes of random data 

    #write the noce to the decrypted firmware memory
    device.write(device.decrypted_firmware_addr, nonce)

    #genereate a noise pattern
    firmware_size = device.N_DH_addr - device.obfuscated_firmware_addr #calculate the firmware size
    
    noise = pseudoCSHAKE256(nonce, firmware_size << 3, b'FIRMWARE OBSCURATION', 
                            device.read(device.device_salt_addr, 32))  # Generate noise based on nonce and device salt.
    
    #calculate the offset for the firmware within the update
    offset = device.downloaded_firmware_addr + len(b'CPSC418 MATH318 W2024') + 3 *16
    offset += ((OS_key_bits + 7) >> 3) #adjust the offset according to OS key size 

    #write the obscured firmware to the decrypted firmware memory 
    device.write(device.decrypted_firmware_addr + len(nonce), xor(noise, device.read(offset, device.N_DH_addr - device.obfuscated_firmware_addr)))

    #flash the new firmware onto the device 
    device.write_firmware(device.decrypted_firmware_addr)

    #zero out the RAM to clear any sensitive data 
    device.zero_RAM()

    #perform a hard reset to finilize the firmware update
    device.hard_reset()

    return 

def create_handshake( device:SecureDevice ) -> bytes:
    """
    Generate the handshake the device sends to the operating system.
      Note that this function does not actually send the handshake,
      and relies on the first stage of the boot process to be complete! 

    PARAMETERS
    ==========
    device: The SecureDevice to draw values from.

    RETURNS
    =======
    The byte sequence to send across the bus for a handshake.
    
    """

    assert isinstance(device, object)

    # the first components are the device and ephemeral public keys,
    #  but we first need to extract their size
    device_key_bits = (device[device.device_N_RSA_addr] << 8) + device[device.device_e_RSA_addr]
    device_key_bytes = ( device_key_bits + 7 ) >> 3

    # since these are in boot ROM, they're available at all times and known to be correct
    device_N = device.read( device.device_N_RSA_addr, device_key_bytes + 1 )
    device_e = device.read( device.device_e_RSA_addr, device_key_bytes + 1 )

    # take the easy way to figuring out the ephemeral key's size
    ephemeral_key_bits = bytes_to_int( device.read( device.ephemeral_key_bits_addr, 4 ) )
    ephemeral_key_bytes = (ephemeral_key_bits + 7) >> 3
    DH_bytes = ((ephemeral_key_bits>>1) + 7)>>3

    p = bytes_to_int( device.read( device.ephemeral_p_RSA_addr, DH_bytes ) )
    q = bytes_to_int( device.read( device.ephemeral_q_RSA_addr, DH_bytes ) )
    ephemeral_N = bytes([ephemeral_key_bits >> 8]) + int_to_bytes( p * q, ephemeral_key_bytes )
    ephemeral_e = device.read( device.ephemeral_e_RSA_addr, ephemeral_key_bytes + 1 )

    # the firmware tag was calculated during the first stage of the boot sequence
    decrypted_firmware_tag = device.read( device.decrypted_firmware_tag_addr, 16 )

    # the signature of the device key and tag of the original model key are in boot ROM
    original_model_key_bits = bytes_to_int( device.read( device.model_key_bits_addr, 4 ) )
    original_model_key_bytes = (original_model_key_bits + 7) >> 3

    device_key_signature = device.read( device.device_RSA_signature_addr, original_model_key_bytes )
    original_model_key_tag = device.read( device.model_key_tag_addr, 16 )

    # the signature of the decrypted firmware tag and ephemeral key are in RAM
    firmware_key_signature = device.read( device.firmware_key_signature_addr, device_key_bytes )

    # time for the Diffie-Hellman parameters
    DH_bytes = ((ephemeral_key_bits >> 1) + 7) >> 3
    N_DH = device.read( device.N_DH_addr, DH_bytes )
    g_DH = device.read( device.g_DH_addr, DH_bytes )

    maximum_messages = device.read( device.maximum_messages_addr, 8 )

    # at last, we have everything we need to create the handshake message
    return device_N[:1] + device_e[:1] + device_N[1:] + device_e[1:] + \
            ephemeral_N[:1] + ephemeral_e[:1] + ephemeral_N[1:] + ephemeral_e[1:] + \
            decrypted_firmware_tag + device_key_signature + original_model_key_tag + \
            firmware_key_signature + N_DH + g_DH + maximum_messages

### END
         
       



def validate_handshake( handshake:bytes, model_key:tuple[bytes,bytes] ) -> \
    Optional[tuple[tuple[bytes,bytes],tuple[bytes,bytes],bytes,tuple[bytes,bytes],int]]:
    """
    Validate the signatures present in the handshake, from the operating system's
      point of view.

    PARAMETERS
    ==========
    handshake: A bytes sequence representing the handshake as it was transmitted.
    model_key: The N and e values of the model RSA key, in byte encoded form, in that
      order.

    RETURNS
    =======
    If the handshake was valid, a tuple consisting of: a tuple of the byte-encoded
      device public key (N and e); a tuple of the byte-encoded ephemeral public key; a tag
      of the decrypted firmware; a tuple of the two Diffie-Hellman parameters (N and g); 
      and an integer giving the maximum number of messages before a re-key. If the
      handshake was invalid, return None.
    """
    assert type(handshake) is bytes
    #print(f"Handshake length: {len(handshake)}")
    assert len(handshake) >= 2*(2*128 + 2) + 16 + 128 + 16 + 128 + 128 + 8 # minimum valid length
    assert type(model_key) is tuple
    assert len(model_key) == 2
    for x in model_key:
        assert type(x) is bytes
    assert len(model_key[0]) == len(model_key[1])

    def carve( value, length ) -> tuple[bytes,bytes]:
        """
        A helper to carve "length" bytes off a bytes object, checking it as well.
        """
        temp = value[:length]
        return (None, value) if len(temp) != length else (temp, value[length:])

    def read_key( value ) -> tuple[bytes,bytes,bytes]:
        """
        A helper to read a public key from the handshake.
        """
        key_sizing, remainder = carve( value, 2 )
        if key_sizing is None:
            return (None,None,value)
        key_bits = bytes_to_int( key_sizing )
        key_bytes = (key_bits + 7) >> 3

        key_N, remainder = carve( remainder, key_bytes )
        if key_N is None:
            return (None,None,value)
        key_N = key_sizing[:1] + key_N     # re-establish the proper encoding

        key_e, remainder = carve( remainder, key_bytes )
        if key_e is None:
            return (None,None,value)
        key_e = key_sizing[1:2] + key_e

        return (key_N, key_e, remainder)

    print("validate_handshake: Starting validation", flush=True)
    device_N, device_e, remainder = read_key( handshake )
    #print(f"validate_handshake: device_N = {device_N.hex()}, device_e = {device_e.hex()}", flush=True)
    if device_N is None:
        return None
    device_key_bits = (device_N[0]<<8) + device_e[0]
    device_key_bytes = (device_key_bits+7) >> 3

    ephemeral_N, ephemeral_e, remainder = read_key( remainder )
    #print(f"validate_handshake: ephemeral_N = {ephemeral_N.hex()}, ephemeral_e = {ephemeral_e.hex()}", flush=True)
    if ephemeral_N is None:
        return None

    # next the tag and device key signature
    decrypted_firmware_tag, remainder = carve( remainder, 16 )
    if decrypted_firmware_tag is None:
        return None

    model_key_bits = (model_key[0][0] << 8) + model_key[1][0]
    model_key_bytes = (model_key_bits + 7) >> 3

    device_key_signature, remainder = carve( remainder, model_key_bytes )
    if device_key_signature is None:
        return None
    if not verify_signed_RSA_key( device_key_signature, model_key, \
            (device_N,device_e), b'DEVICE' ):
        return None

    # the original model key tag
    original_model_key_tag, remainder = carve( remainder, 16 )
    if original_model_key_tag is None:
        return None
    model_tag = pseudoCSHAKE256( b''.join(model_key), 16 << 3, b'PUBLIC KEY', b'MODEL' )
    if original_model_key_tag != model_tag:
        return None

    # verify the firmware key signature
    ephemeral_key_bits = (ephemeral_N[0] << 8) + ephemeral_e[0]
    ephemeral_key_bytes = (ephemeral_key_bits + 7) >> 3
    firmware_key_signature, remainder = carve( remainder, device_key_bytes )
    if firmware_key_signature is None:
        return None

    expected = pseudoCSHAKE256( decrypted_firmware_tag + ephemeral_N + ephemeral_e, \
            (len(device_N) - 2) << 3, b'FIRMWARE EPHEMERAL TAG' )

    if not verify_RSA( firmware_key_signature, expected, device_N, device_e ):
        return None

    # grab N, g, and the maximum number of messages
    DH_bytes = ((ephemeral_key_bits >> 1) + 7) >> 3
    N_DH, remainder = carve( remainder, DH_bytes )
    if N_DH is None:
        return None
    g_DH, remainder = carve( remainder, DH_bytes )
    if g_DH is None:
        return None
    
    max_messages, remainder = carve( remainder, 8 )
    if max_messages is None:
        return None

    return ( (device_N,device_e), (ephemeral_N,ephemeral_e), decrypted_firmware_tag, \
        (N_DH, g_DH), bytes_to_int(max_messages) )
    
def stage_one_boot( device:SecureDevice ) -> bool:
    """
    Perform the first stage of the boot process, as outlined in the assignment.
      You should assume that the boot ROM and encrypted firmware are present,
      but nothing else. Note that this process modifies the SecureDevice
      given as a parameter.


    PARAMETERS
    ==========
    device: The SecureDevice to draw values from.

    RETURNS
    =======
    True if successful, False on failure.
    """
    assert isinstance(device, object)

    #clear the device's RAM to ensure no leftover data remains.
    device.zero_RAM()

    #generate noise to de-obfuscate the firmware 
    #calculate the size of the firmware based on known memory address. 
    firmware_size = device.N_DH_addr - device.obfuscated_firmware_addr

    #read the nonce and used it 
    nonce = device.read( device.firmware_nonce_addr, 32 )
    noise = pseudoCSHAKE256( nonce, firmware_size << 3, b'FIRMWARE OBSCURATION', \
            device.read( device.device_salt_addr, 32 ) )
    
    # de-obfuscate the firmware
    firmware_blob = xor( noise, \
            device.read( device.obfuscated_firmware_addr, firmware_size ) )
    
    #Decrypt the de-obfuscated firmware.
    # Calculate the size of the RSA key used for decryption.
    #firmware_blob = xor(noise, device.read(device.obfuscated_firmware_addr, firmware_size))
    firmware_key_bits = (device[device.firmware_N_RSA_addr]<<8) + device[device.firmware_e_RSA_addr]
    firmware_key_bytes = (firmware_key_bits + 7) >> 3

    # Read the RSA public key (N and e) used for decryption.
    firmware_N = device.read( device.firmware_N_RSA_addr, firmware_key_bytes + 1 )
    firmware_e = device.read( device.firmware_e_RSA_addr, firmware_key_bytes + 1 )

    # Decrypt the first portion of the firmware blob to extract the password.
    firmware_password = encrypt_RSA( firmware_blob[:firmware_key_bytes], firmware_N, firmware_e )
    
    # Perform a basic sanity check to ensure the password starts with a zero byte.
    if firmware_password[0] != 0:
        return False
    
    # Remove the leading zero byte.
    firmware_password = firmware_password[1:]

    # Use the password to decrypt and verify the rest of the firmware.
    decrypted_firmware = decrypt_and_verify( firmware_blob[firmware_key_bytes:], firmware_password, \
            32 << 3, 16 << 3, len(firmware_password) << 3 )
    # If decryption fails, return False.
    if decrypted_firmware is None:
        return False

    # Store the decrypted firmware in RAM and generate its tag.
    device.write(device.decrypted_firmware_addr, decrypted_firmware)
    
    # Generate a tag for the decrypted firmware to ensure its integrity.
    decrypted_firmware_tag = pseudoCSHAKE256(decrypted_firmware, 16 << 3, b'FIRMWARE TAG')
    device.write(device.decrypted_firmware_tag_addr, decrypted_firmware_tag)

    # Generate Diffie-Hellman parameters for secure key exchange.
    # Determine the size of the ephemeral RSA key.
    ephemeral_key_bits = bytes_to_int(device.read(device.ephemeral_key_bits_addr, 4))
    ephemeral_key_bytes = (ephemeral_key_bits + 7) >> 3
    DH_bytes = ((ephemeral_key_bits >> 1) + 7) >> 3

    # Use the device's cryptographically secure random number generator (CSPRNG) and prime checker to generate a safe prime for Diffie-Hellman.
    rng = DeviceCSPRNG(device)
    prim = PrimeChecker()

    N = safe_prime(DH_bytes << 3, rng, prim)
    N_DH = int_to_bytes(N, DH_bytes)
    device.write(device.N_DH_addr, N_DH)

    # Calculate the primitive root (g) for the Diffie-Hellman group.
    g = prim_root(bytes_to_int(N_DH))
    g_DH = int_to_bytes(g, DH_bytes)
    device.write(device.g_DH_addr, g_DH)

    # Ensure the message count is initialized to zero.
    device.write(device.message_count_addr, bytes(8))

    # Generate an ephemeral RSA key for temporary secure communication.
    ephemeral_params = generate_pq_RSA( ephemeral_key_bits, device )
    ephemeral_N, ephemeral_e, ephemeral_d = generate_RSA_key( *ephemeral_params, device )

    # Store the ephemeral RSA parameters in memory.
    device.write(device.ephemeral_p_RSA_addr, ephemeral_params[0])
    device.write(device.ephemeral_q_RSA_addr, ephemeral_params[1])
    device.write(device.ephemeral_e_RSA_addr, ephemeral_e)
    device.write(device.ephemeral_d_RSA_addr, ephemeral_d)

    # Sign the ephemeral key using the device's RSA key.
    # Calculate the size of the device's RSA key.
    device_key_bits = (device[device.device_N_RSA_addr] << 8) + device[device.device_e_RSA_addr]
    device_key_bytes = (device_key_bits + 7) >> 3

    # Read the device's RSA key components (N, e, and d).
    device_N = device.read(device.device_N_RSA_addr, device_key_bytes + 1)
    device_e = device.read(device.device_e_RSA_addr, device_key_bytes + 1)
    device_d = device.read(device.device_d_RSA_addr, device_key_bytes)

    # Generate a value to sign, including the decrypted firmware tag and ephemeral key components.
    value = pseudoCSHAKE256( decrypted_firmware_tag + ephemeral_N + ephemeral_e, \
            (len(device_N) - 2) << 3, b'FIRMWARE EPHEMERAL TAG' )
    # Sign the value with the device's RSA key.
    signed_firmware = sign_RSA( value, device_N, device_e, device_d )
    device.write( device.firmware_key_signature_addr, signed_firmware )

    # Finalize the boot process.
    # Lock the boot ROM to prevent further modifications.
    device.lock_ROM()
    
    # Jump to the start of the decrypted firmware code to continue booting.
    device.jump_to_decrypted_code()

    return True


    

def device_shared_key( sock:socket.socket, device:SecureDevice ) -> bool:
    """
    Negotiate a shared key from the point of view of the device.
      You may assume the handshake has already been sent. Note that this
      routine does not preserve the original state of the device! Do not
      close the socket in the event of an error, the template does that
      for you.

    PARAMETERS
    ==========
    sock: The socket used to emulate a data bus. Must be connected.
    device: The SecureDevice negotiating the key.

    RETURNS
    =======
    True if a key could be negotiated, False otherwise.
    """
    assert type(sock) is socket.socket
    assert isinstance(device, object)

    # Initialize the message count to 1 for the shared key negotiation.
    # The message count is reset to 1 for each key negotiation, as per the specification.
    device.write(device.message_count_addr, int_to_bytes(1, 8))

    # Convert the device's parameters into a format that Assignment 2's code can handle.
    # This function extracts the current state of the device and prepares it for key negotiation.
    cp, sp = device_to_parameters(device)

    # Set up a database of client parameters, indexed by the password (p).
    # This database is used to match incoming requests during key negotiation.
    database = {cp.p: cp}

    # Use the device's cryptographically secure random number generator (CSPRNG) for randomness.
    rng = DeviceCSPRNG(device)

    # Begin the server-side key negotiation process using the provided socket.
    # The server_key function handles the bulk of the Diffie-Hellman exchange and key negotiation.
    result = server_key(sock, sp, database, rng)
    
    # If the negotiation fails, return False.
    if result is None:
        return False

    # Extract the negotiated parameters (SP, DATABASE) from the result.
    SP, DATABASE = result
    CP = DATABASE[cp.p]

    # Write the negotiated parameters back to the device's memory.
    # This updates the device with the new shared key and any other negotiated values.
    parameters_to_device(device, CP, SP)

    return True


def os_shared_key( sock:socket.socket, cp:ClientParameters, sp:ServerParameters, \
        rng:FastCSPRNG ) -> bool:
    """
    Negotiate a shared key from the point of view of the operating system.
      You may assume the handshake has already been sent. Note that this
      routine alters the original objects, unlike A2's philosophy. Do not close
      the socket in the event of an error, the template does that for you.

    PARAMETERS
    ==========
    sock: The socket used to emulate a data bus. Must be connected.
    cp: The ClientParameters object representing the OS's current knowledge.
    sp: The ServerParameters object serving the same purpose as the above.
    rng: A FastCSPRNG to use when generating randomness.

    RETURNS
    =======
    True if a key could be negotiated, False otherwise.
    """
    assert type(sock) is socket.socket
    assert isinstance(cp, object)
    assert isinstance(sp, object)
    assert isinstance(rng, object)

    # reset the message count to 1 for both client and server parameters
    cp.message_count = 1
    sp.message_count = 1

    #Use the client function to attempt the negotiation of the shared key 
    result = client_key(sock, cp, sp, rng)

    #f the result is None, the negotiation failed, and the function should return False
    if result is None:
        return False
    
    #unpack the result
    CP, SP = result

    # Update the client parameters with the new values received from the server.
    for attr in ['a', 'A', 's', 'u', 'K_client', 'Y', 'M1', 'message_count']:
        setattr(cp, attr, getattr(CP, attr))
    
    # Similarly, update the server parameters with the new values.
    for attr in ['B', 'K_server', 'message_count']:
        setattr(sp, attr, getattr(SP, attr))

    return True
    
def check_device_shared_key(sock, device):
    """
    A helper to check if key re-negotiation needs to happen, from the device's
    point of view, and then do it.

    PARAMETERS
    ==========
    sock: The socket used to emulate a data bus.
    device: The SecureDevice that may need to renegotiate its key.

    RETURNS
    =======
    True if the current key is valid or re-negotiation succeeds, False otherwise.
    """
    
    # Read the current message count from the device's memory.
    current_messages = bytes_to_int(device.read(device.message_count_addr, 8))
    
    # Read the maximum allowed message count before re-negotiation is required.
    max_messages = bytes_to_int(device.read(device.maximum_messages_addr, 8))

    # If the current message count exceeds or equals the maximum, renegotiate the key.
    if current_messages >= max_messages:
        result = device_shared_key(sock, device)
        
        # If key re-negotiation fails, return False.
        if not result:
            return False

    # If no re-negotiation is needed or it succeeds, return True.
    return True


def device_to_os( sock:socket.socket, device:SecureDevice, data:bytes ) -> bool:
    """
    Pass information to the operating system from the device, from the point of
      view of the device. Ensure that if a shared key needs to be re-negotiated, 
      the device does that before sending the data. You may assume the handshake 
      has already been sent.

    PARAMETERS
    ==========
    sock: The socket used to emulate a data bus. Must be connected.
    device: The SecureDevice negotiating the key.
    data: The byte sequence to send to the operating system.

    RETURNS
    =======
    True if the data could be sent, False otherwise.
    """
    assert type(sock) is socket.socket
    assert isinstance(device, object)
    assert type(data) is bytes

    # Check if the device needs to renegotiate the shared key before sending data.
    if not check_device_shared_key(sock, device):
        return False

    # Convert the device's current state into ClientParameters and ServerParameters.
    cp, sp = device_to_parameters(device, "", 1)  # The IP and port are not used here.

    # Send the data using the client_file function.
    CP = client_file(sock, cp, sp, data)
    
    # If the data transmission fails, return False.
    if CP is None:
        return False

    # Update the device's parameters with the new values received from the OS.
    parameters_to_device(device, CP, sp)
    
    # Return True if data was successfully sent and parameters updated.
    return True

def check_os_shared_key( sock, cp, sp, rng, max_messages ):
    """
    A helper to check if we need to renegotiate a shared key, from the operating
      system's side of things, and then do it if necessary.
    """
    #check if the OS's message count has reched or exceeded the maximum allowed 
    if cp.message_count >= max_messages:
        #if so, attend renegotiate the shared key 
        result = os_shared_key( sock, cp, sp, rng )
        #if the renegotiation failed return false
        if not result:
            return False
    
    #if no renegotiation is needed or it succeds, return true
    return True

def os_to_device( sock:socket.socket, cp:ClientParameters, sp:ServerParameters, \
        rng:FastCSPRNG, max_messages:int, data:bytes ) -> bool:
    """
    Pass information to the device from the operating system, from the point of the
      operating system. Ensure that if a shared key needs to be re-negotiated, the 
      computer initiates that before sending the data. You may assume the handshake 
      has already been sent.

    PARAMETERS
    ==========
    sock: The socket used to emulate a data bus. Must be connected.
    cp: The ClientParameters object representing the OS's current knowledge.
    sp: The ServerParameters object serving the same purpose as the above.
    rng: A FastCSPRNG to use when generating randomness.
    max_messages: The maximum number of messages to send before renegotiating the key.
    data: A bytes sequence to send.

    RETURNS
    =======
    True if the data was sent successfully, False otherwise.
    """
    assert type(sock) is socket.socket
    assert isinstance(cp, object)
    assert isinstance(sp, object)
    assert isinstance(rng, object)
    assert type(max_messages) is int
    assert max_messages >= 0
    assert type(data) is bytes

    # check if key needs to be renegotiate before sending data
    if not check_os_shared_key(sock, cp, sp, rng,max_messages):
        return False
    
    #send the data to the device using the client file function
    CP = client_file(sock, cp, sp, data)

    # if the data transmission fails, return false
    if CP is None:
        return False

    #update the server's messade count to match the client's after transmission 
    sp.message_count = CP.message_count

    #update the client paramaters 
    for attr in ['a', 'A', 's', 'u', 'K_client', 'Y', 'M1', 'message_count']:
        setattr(cp, attr, getattr(CP, attr))
    # sp was updated via os_shared_key
    return True



def device_from_os( sock:socket.socket, device:SecureDevice ) -> Optional[bytes]:
    """
    Pass information from the operating system to the device, from the point of view
      of the device. Ensure that if a shared key needs to be re-negotiated, the 
      device does that before sending the data. You may assume the handshake has 
      already been sent.

    PARAMETERS
    ==========
    sock: The socket used to emulate a data bus. Must be connected.
    device: The SecureDevice negotiating the key.

    RETURNS
    =======
    The byte sequence sent, if successful, otherwise None.
    """
    assert type(sock) is socket.socket
    assert isinstance(device, object)

    # check if key needs to be renegotiate before sending data
    if not check_device_shared_key(sock, device):
        return None

    #convert the device's current state into client parameters and server parameters
    cp, sp = device_to_parameters(device, "", 1) #IP and port placeholder 

    #prepare the database containing the current client paramaters, indexed by the client's 'p' value
    database = {cp.p: cp}

    #use the server_file function to recieve info from OS
    result = server_file(sock, sp, database)
    if result is None:
        return None  #failed transmission 
    
    #unpack the result into updated server parameters (S), client 'p' value, and received filed 
    SP, p, file = result

    #update message count, assures synchronisity
    cp.message_count = SP.message_count
    sp.message_count = SP.message_count

    #update the device's parameters with the new values received
    parameters_to_device(device, cp, sp)

    #return the received file (Byte sequence) if successful 
    return file
    
     

def os_from_device( sock:socket.socket, cp:ClientParameters, sp:ServerParameters, \
        rng:FastCSPRNG, max_messages:int ) -> Optional[bytes]:
    """
    Pass information from the device to the operating system, from the point of view
      of the operating system. Ensure that if a shared key needs to be re-negotiated, 
      the computer initiates that before sending the data. You may assume the 
      handshake has already been sent.

    PARAMETERS
    ==========
    sock: The socket used to emulate a data bus. Must be connected.
    cp: The ClientParameters object representing the OS's current knowledge.
    sp: The ServerParameters object serving the same purpose as the above.
    rng: A FastCSPRNG to use when generating randomness.
    max_messages: The maximum number of messages to send before renegotiating the key.

    RETURNS
    =======
    The byte sequence sent, if successful, otherwise None.
    """

    # Check if the shared key needs to be renegotiated before receiving data.
    if not check_os_shared_key(sock, cp, sp, rng, max_messages):
        return None  # Return None if renegotiation fails or is required but not done.
    
    #prepare a database containing the current client parameters, indecex by the clients 'p' value
    database = {cp.p: cp}

    # use the 'server_file' function to received the dat from the device 
    result = server_file(sock, sp, database)
    if result is None:
        return None # None, if transmission failed
    
    #unpack the results into updated Serverparameters (SP), the client 'p' value, and the file 
    SP, p, file = result

    #update message count, syncronizity
    cp.message_count = SP.message_count
    sp.message_count = SP.message_count

    #return the received file(byte sequence)
    return file 


##### MAIN

if __name__ == '__main__':


    start = time()      # we might need this for the timeout

    # parse the command line arguments
    cmdline = argparse.ArgumentParser( description="Test out a secure device communication protocol." )
    cmdline.add_argument( 'image', metavar='FILE', type=Path, \
        help="A replica of the SecureDevice's memory, as a JSON file compressed with gzip. Mandatory." )

    options = cmdline.add_argument_group( 'OPTIONS', "Modify the defaults used when exercising this protocol." )
    options.add_argument( '--firmware', metavar='FILE', type=Path, \
        help="A firmware upgrade to apply to the SecureDevice." )
    options.add_argument( '--addr', metavar='IP:PORT', type=str, default="127.0.4.18:3180", \
        help='The IP address and port used to emulate the USB port.' )
    options.add_argument( '--timeout', metavar='SECONDS', type=int, default=300, \
        help='How long until the program automatically quits. Negative or zero disables this.' )
    options.add_argument( '--test_rekey', action='store_true', \
        help="Test that a new shared key is negotiated after the maximum number of messages is reached." )
    options.add_argument( '-v', '--verbose', action='store_true', \
        help="Be more verbose about what is happening." )

    args = cmdline.parse_args()


    if args.verbose:
        print(f"Program: Checking the consistency of parameters.")

    if not args.image.exists():
        print("Program: ERROR: the image file must exist")
        exit(1)
    if (args.firmware is not None) and (not args.firmware.exists()):
        print("Program: ERROR: if given, the firmware image must exist")
        exit(1)

    result = split_ip_port( args.addr )
    if type(result) is not tuple:
        print("Program: ERROR: ensure the IP:port combination is valid")
        exit(1)
    IP, port = result

    if args.verbose:
        print(f"Program: Creating the simulated secure device.")

    with gzip.open( args.image, 'rt' ) as zfile:
        image_details = json.load( zfile )

    if 'memory' not in image_details:
        print("Program: ERROR: the image must contain a hexadecimal representation of the device")
        exit(1)
    device_image = bytes.fromhex( image_details['memory'] )

    if 'bounds' not in image_details:
        print("Program: ERROR: the image must contain the bounds of the SecureDevice")
        exit(1)
    if sum( image_details['bounds'] ) != len( device_image ):
        print("Program: ERROR: the memory pools must add up to the total bytes stored in the image")
        exit(1)

    if 'key_reserve' not in image_details:
        print("Program: ERROR: the image must contain the maximal expected size of an RSA key")
        exit(1)
    if image_details['key_reserve'] < 1024:
        print("Program: ERROR: the maximal RSA key size is positive and reasonable")
        exit(1)
    # RSA Labs considered 1,024-bit keys insecure by 2010, FYI, and 15,360-bit RSA is 
    #  considered as secure as a 256-bit symmetric encryption key (NIST SP 800-57)

    device = SecureDevice( bounds=image_details['bounds'], key_reserve=image_details['key_reserve'], \
            state=device_image )

    if args.verbose:
        print(f"Program: Triggering stage one of the boot process.")

    def perform_boot( device ):
        """
        A helper to boot up the device.
        """

        result = stage_one_boot( device )
        if not result:
            print( f"Program: ERROR: Failed to complete the boot process." )
            exit(1)

    perform_boot( device )

    if args.firmware:
        if args.verbose:
            print(f"Program: Preparing to upgrade the device firmware.")

        with open( args.firmware, 'rb' ) as file:
            firmware_update_bundle = file.read()

        device.write( device.downloaded_firmware_addr, firmware_update_bundle )
        if not verify_firmware(device):
            print(f"Program: The firmware update was invalid, wiping the device.")
            device.zero_RAM()
            device.hard_reset()
        else:
            if args.verbose:
                print(f"Program: The firmware update validated, applying it and rebooting.")
            update_firmware( device )

        perform_boot( device )

    if args.verbose:
        print(f"Program: Preparting to launch the simulated protocol.")

    # we need the model key for the operating system
    model_key_bits = (device[device.model_N_RSA_addr]<<8) + device[device.model_e_RSA_addr]
    model_key_bytes = (model_key_bits + 7) >> 3

    model_N = device.read( device.model_N_RSA_addr, model_key_bytes + 1 )
    model_e = device.read( device.model_e_RSA_addr, model_key_bytes + 1 )

    # and we should extract A2 parameters from the device
    cp, sp = device_to_parameters( device, IP, port )


    if args.verbose:
        print(f"Program: Launching the USB simulation.")

    def disconnect( client, verbose ):
        """A lemma to help with disconnection."""
        if verbose:
            print( f"OS: Closing connection to the device.", flush=True )
        client.close()

    device_thread = None
    def device_loop( device, IP, port, rekey, verbose ):

        sock     = create_socket( IP, port, listen=True )
        if sock is None:
            print( "Device: Could not create socket, quitting.", flush=True )
            return

        client, client_address = sock.accept()
        if verbose:
            print( f"Device: Was connected to from {client_address}.", flush=True )
            print( "Device: About to send the handshake to the OS.", flush=True )

        handshake = create_handshake( device )
        message = create_message( handshake, 0, b'', 16 )

        result = send( client, message )
        if result != len(message):
            print( f"Device: Could not send the handshake, exiting.", flush=True )
            disconnect( client, verbose )
            return disconnect( sock, verbose )

        if verbose:
            print( "Device: Preparing for the OS to register.", flush=True )

        _, sp = device_to_parameters( device )
        sp.message_count = 1
        sp.k = calc_k( sp )

        result = server_register( client, sp, dict() )
        if result is None:
            print( f"Device: Registration failed, exiting.", flush=True )
            disconnect( client, verbose )
            return disconnect( sock, verbose )

        if verbose:
            print( "Device: Registration successful, updating the device.", flush=True )

        SP, database = result
        assert len(database) == 1
        for key in database:
            CP = database[key]

        parameters_to_device( device, CP, SP )

        if verbose:
            print( "Device: Preparing to reach a shared key.", flush=True )

        if not device_shared_key( client, device ):
            print( f"Device: Could not negotiate a shared key with the OS, aborting.", flush=True )
            disconnect( client, verbose )
            return disconnect( sock, verbose )

        # send/receieve loop
        if rekey:
            loops = (bytes_to_int(device.read( device.maximum_messages_addr, 8 ))>>2) + 2
        else:
            loops = 1
        if verbose:
            print( f"Device: Performing the send/receive loop {loops} time(s).", flush=True )

        rng = DeviceCSPRNG( device )        # needed to figure out how much to send

        for _ in range(loops):

            message_length = bytes_to_int( rng.get(2) ) 
            message = rng.get( message_length )

            if verbose:
                status = f"starting with 0x{message[:16].hex()}..." if len(message) > 16 \
                    else f"consisting of 0x{message.hex()}."

                print( f"Device: Sending a {message_length}-byte message to the OS, {status}", flush=True )

            if not device_to_os( client, device, message ):
                print( f"Device: Could not send a message to the OS, aborting.", flush=True )
                disconnect( client, verbose )
                return disconnect( sock, verbose )

            if verbose:
                print( f"Device: Current message count is {bytes_to_int(device.read(device.message_count_addr,8))}", flush=True )
                print( "Device: Receiving a message from the OS.", flush=True )

            result = device_from_os( client, device )
            if type(result) is not bytes:
                print( f"Device: Could not receive data from the OS, aborting.", flush=True )
                disconnect( client, verbose )
                return disconnect( sock, verbose )
            elif verbose:
                status = f"starting with 0x{result[:16].hex()}..." if len(result) > 16 \
                    else f"consisting of 0x{result.hex()}."

                print( f"Device: Received {len(result)} bytes from the OS, {status}", flush=True )
                print( f"Device: Current message count is {bytes_to_int(device.read(device.message_count_addr,8))}", flush=True )

        if verbose:
            print( f"Device: Finished the loop, cleaning up.", flush=True )
        disconnect( client, verbose )
        return disconnect( sock, verbose )

    if args.verbose:
        print( "Program: Launching the device side of the simulation.", flush=True )
    device_thread = Thread( target=device_loop, args=(device, IP, port, args.test_rekey, args.verbose) )
    device_thread.daemon = True
    device_thread.start()


    os_thread = None
    def os_loop( cp, sp, model_key, rekey, verbose ):

        sock     = create_socket( sp.ip, sp.port )
        if sock is None:
            print( "OS: Could not create socket, quitting.", flush=True )
            return

        if verbose:
            print( "OS: Reading in the handshake.", flush=True )

        handshake = receive_message( sock, 16, 0, b'' )

        #testing
        #if verbose:
          #  print(f"OS: Received handshake of length {len(handshake)}: {handshake.hex()}", flush=True)

        if handshake is None:
            print( f"OS: No handshake message received, aborting.", flush=True )
            return disconnect( sock, verbose )

        results = validate_handshake( handshake, model_key )
        if results is None:
            print( f"OS: Invalid handshake received, aborting.", flush=True )
            return disconnect( sock, verbose )

        if verbose:
            print( "OS: Unpacking and updating the A2 objects.", flush=True )

        device_key, ephemeral_key, decrypted_firmware_tag, DH_params, max_messages = results
        device_N, device_e = device_key
        ephemeral_N, ephemeral_e = ephemeral_key

        cp.message_count = 1        # handshake is always message zero

        sp.message_count = cp.message_count
        sp.N, sp.g = DH_params
        sp.k = calc_k( sp )


        if verbose:
            print( "OS: Registering with the device.", flush=True )

        rng = FastCSPRNG()
        cp.username = rng.get( sp.int_bytes ).hex()     # fill in any old thing
        cp.pw = rng.get( sp.int_bytes ).hex()

        result = client_register( sock, cp, sp, rng )
        if result is None:
            print( f"OS: Could not register with device, aborting.", flush=True )
            return disconnect( sock, verbose )

        cp, sp = result     # erase the old values

        if verbose:
            print( "OS: Negotiating the first shared key.", flush=True )

        if not os_shared_key( sock, cp, sp, rng ):
            print( f"OS: Could not negotiate a shared key with device, aborting.", flush=True )
            return disconnect( sock, verbose )

        loops = (max_messages>>2) + 2 if rekey else 1
        if verbose:
            print( f"OS: Performing the receieve/send loop {loops} time(s).", flush=True )

        for _ in range(loops):
            if verbose:
                print( "OS: Receiving a message from the device.", flush=True )

            result = os_from_device( sock, cp, sp, rng, max_messages )
            if type(result) is not bytes:
                print( f"OS: Could not receive data from the device, aborting.", flush=True )
                return disconnect( sock, verbose )
            elif verbose:
                status = f"starting with 0x{result[:16].hex()}..." if len(result) > 16 \
                    else f"consisting of 0x{result.hex()}."

                print( f"OS: Received {len(result)} bytes from the device, {status}", flush=True )
                print( f"OS: Current message count is {cp.message_count}", flush=True )

            message_length = bytes_to_int( rng.get(2) ) 
            message = rng.get( message_length )

            if verbose:
                status = f"starting with 0x{message[:16].hex()}..." if len(message) > 16 \
                    else f"consisting of 0x{message.hex()}."

                print( f"OS: Sending a {message_length}-byte message to the device, {status}", flush=True )

            if not os_to_device( sock, cp, sp, rng, max_messages, message ):
                print( f"OS: Could not receive data from device for message, aborting.", flush=True )
                return disconnect( sock, verbose )

            if verbose:
                print( f"OS: Current message count is {cp.message_count}", flush=True )

        if verbose:
            print( f"OS: Finished the loop, cleaning up.", flush=True )
        return disconnect( sock, verbose )

    if args.verbose:
        print( "Program: Launching the OS side of the simulation.", flush=True )
    os_thread = Thread( target=os_loop, args=(cp, sp, (model_N,model_e), args.test_rekey, args.verbose) )
    os_thread.daemon = True
    os_thread.start()


    # finally, we wait until we're told to kill ourselves off, or both sides have finished communicating
    while not ((device_thread is None) and (os_thread is None)):

        if (os_thread is not None) and (not os_thread.is_alive()):
            if args.verbose:
                print( f"Program: The operating system side of the protocol has terminated.", flush=True )
            os_thread = None
        
        if (device_thread is not None) and (not device_thread.is_alive()):
            if args.verbose:
                print( f"Program: The device side of the protocol has terminated.", flush=True )
            device_thread = None
 
        if args.timeout > 0:
            delta = time() - start
            if delta > args.timeout:
                print( f"Program: Timeout reached, forcing a shutdown.", flush=True )
                exit()

        sleep( 0.1 )    # compromise between responsiveness and letting each process cook
