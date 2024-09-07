#!/usr/bin/env python3

##### IMPORTS

from __future__ import annotations

import argparse
from dataclasses import dataclass
from pathlib import Path
import socket
from sys import exit
from tempfile import TemporaryDirectory
from threading import Thread
from time import sleep
from typing import Any, Callable, Iterator, Mapping, Optional, Union

from Crypto.Cipher import AES
from hashlib import scrypt
from os import urandom
import numpy as np
from sympy import isprime

# these functions carry over from the prior assignment
from encrypt_decrypt__SOLUTION import left_encode, pseudoCSHAKE256
from encrypt_decrypt__SOLUTION import MAC_then_encrypt, decrypt_and_verify

# If you need to import anything, insert it here
### BEGIN

# implement the prime sieve of Wiener[2003]
prime_list = [5]
target = 128

while len(prime_list) < target:

    cand = prime_list[-1] + ((1 - prime_list[-1]) % 6)  # adjust to 1 mod 6
    increment = 4                       # jump from 1 mod 6 to 5 mod 6

    while (cand <= prime_list[-1]) or (not isprime(cand)):

        cand += increment
        increment = 2 if increment == 4 else 4      # toggle between 5 mod 6 and 1 mod 6

    prime_list.append( cand )

### END

##### CLASSES

class FastCSPRNG:
    """
    As the name implies, a fast cryptographically-secure pseudo-random number generator.
      Proof that it is cryptographically-secure is left up to the student. Note that merely
      being cryptographically-secure does not mean this code is flawless!
    """

    def __init__(self, seed=None):
        """
        Create and initialize a FastCSPRNG.

        PARAMETERS
        ==========
        seed: A bytes object to use as a seed. Optional, the default seeds from a cryptographically-secure source.
        """

        self._counter = 0                   # what to encrypt
        self._buffer = b''
        self._block_bits = 128              # AES's block size, in bits
        self._block_bytes = self._block_bits >> 3

        if type(seed) is not bytes:         # sensible default
            seed = urandom(32)

        self._seed = pseudoCSHAKE256( seed, 128 )      # compensate for seeds that are too long or short
        self._generator = AES.new( self._seed, AES.MODE_ECB ).encrypt

    def _inc(self):
        self._buffer += self._generator( self._counter.to_bytes(self._block_bytes,'big') )
        self._counter += 1
        self._counter &= (1 << self._block_bits) - 1     # ensure the conversion to bytes always works

    @property
    def bytes_generated(self):
        """
        Return the number of bytes generated, as an integer. Not necessarily the same as the number of bytes returned!
        """
        return self._counter * self._block_bytes

    def get(self, b):
        """
        Return 'b' bytes of cryptographically-secure pseudo-random data.
        """
        assert type(b) is int
        assert b > 0

        while len(self._buffer) < b:
            self._inc()

        retVal = self._buffer[:b]
        self._buffer = self._buffer[b:]     # save unneeded values for future use

        return retVal


class PrimeChecker:
    """
    A thin wrapper around sympy.isprime() that only exists to gather statistics on the number of times
      it is called.
    """

    def __init__(self):

        self._count = 0

    @property
    def count(self):
        return self._count

    def isprime(self, x):
        """
        Check if the given integer, x, is prime.
        """
        # assert type(x) is int         # disable these for speed
        # assert x > 1

        self._count += 1
        return isprime( x )


@dataclass
class ServerParameters:
    """
    Collect all the data associated with the Server. This makes it much easier to pass data
      into and out of functions. Most fields are optional, since this structure is used by 
      the Client as well but there are a lot of values it cannot know.

    EXAMPLE
    =======

    >> sp = ServerParameters( 96, 32, 32, "127.0.0.1", 4318 )
    >> sp.tag_bytes == 32
    True
    >> sp.int_bytes
    96
    >> sp.N
    None

    """
    int_bytes:  int     # how many bytes do integers take up?
    tag_bytes:  int     # the byte length of the tag
    salt_bytes: int     # and so on

    ip:   str              # the IP address of the Server
    port: int              # the port the Server is listening on

    message_count: int = 0      # the number of the next message, incoming or outgoing

    N: Union[bytes,int] = None  # the safe prime used for Diffie-Hellman
    g: Union[bytes,int] = None  # a primitive root used for the above
    k: Union[bytes,int] = None  # see the assignment sheet

    b: Union[bytes,int] = None       # a random value used for DH
    B: Union[bytes,int] = None

    K_server: Union[bytes,int] = None        # what the Server thinks the shared key is
    u:        Union[bytes,int] = None        # see the assignment sheet for these
    Y:        Union[bytes,int] = None
    M1:       Union[bytes,int] = None

    def clone(self):
        """
        Create a copy of the current ServerParamaters. Handy for use in the higher-level
          routines. Note that message_count isn't cloned!

        RETURNS
        =======
        A clone of the current ServerParameters.
        """
        retVal = ServerParameters( self.int_bytes, self.tag_bytes, self.salt_bytes, self.ip, self.port )
        for attr in ['N','g','k','b','B','K_server','u','Y','M1']:
            setattr(retVal, attr, getattr(self, attr))
        return retVal

    @staticmethod
    def read(file) -> Optional[ServerParameters]:
        """
        Read in ServerParameters from a file. pickle makes this a lot easier, but has
          security issues, hence why this method exists.

        PARAMETERS
        ==========
        file: A file-like object to read text from.

        RETURNS
        =======
        A ServerParameters object, if the input could be read, or None otherwise.
        """
        import json

        try:
            t = json.load( file )
            retVal = ServerParameters( *[t[x] for x in ['int_bytes','tag_bytes','salt_bytes','ip','port']] )
        except:
            return None

        for attr in ['N','g','k','b','B','K_server','u','Y','M1']:
            if attr in t:
                if type( t[attr] ) is str:
                    setattr( retVal, attr, int(t[attr], 16) )
                elif type( t[attr] ) is int:
                    setattr( retVal, attr, t[attr] )
                else:
                    return None

        return retVal

    def write(self, file) -> bool:
        """
        Write out ServerParameters to a file. pickle makes this a lot easier, but has
          security issues, hence why this method exists.

        PARAMETERS
        ==========
        file: A file-like object to write text to.

        RETURNS
        =======
        True if successful, false otherwise.
        """
        import json

        temp = { attr:getattr(self,attr) for attr in ['int_bytes','tag_bytes','salt_bytes','ip','port'] }
        for attr in ['N','g','k','b','B','K_server','u','Y','M1']:
            value = getattr(self,attr)
            if type(value) is int:
                temp[attr] = value
            elif type(value) is bytes:
                temp[attr] = value.hex()

        try:
            json.dump( temp, file )
        except:
            return False
        
        return True


@dataclass
class ClientParameters:
    """
    Collect all the data associated with the Server. This makes it much easier to pass data
      into and out of functions. Most fields are optional, since this structure is used by 
      the Server as well but there are a lot of values it cannot know.

    EXAMPLE
    =======

    >> cp = ClientParameters( s=b'CPSC 418 MATH 318' )
    >> cp.s == b'CPSC 418 MATH 318'
    True
    >> cp.p
    None

    """
    s: bytes = None        # the salt associated with this Client
    
    message_count: int = 0      # the number of the next message, incoming or outgoing

    username: str = None
    pw:       str = None                # the Client's password
    x:        Union[bytes,int] = None   # see the assignment sheet
    v:        Union[bytes,int] = None
    p:        Union[bytes,int] = None   # derived from the password

    a: Union[bytes,int] = None       # a random value used for DH
    A: Union[bytes,int] = None

    K_client: Union[bytes,int] = None    # what the Client thinks is the shared key
    u:        Union[bytes,int] = None    # and so on
    Y:        Union[bytes,int] = None
    M1:       Union[bytes,int] = None

    def clone(self):
        """
        Create a copy of the current ClientParamaters. Handy for use in the higher-level
          routines. Note that message_count isn't cloned!

        RETURNS
        =======
        A clone of the current ClientParameters.
        """
        retVal = ClientParameters()
        for attr in ['s','username','pw','x','v','p','a','A','K_client','u','Y','M1']:
            setattr(retVal, attr, getattr(self, attr))
        return retVal

    @staticmethod
    def read(file):
        """
        Read in ClientParameters from a file. pickle makes this a lot easier, but has
          security issues, hence why this method exists.

        PARAMETERS
        ==========
        file: A file-like object to read text from.

        RETURNS
        =======
        A ClientParameters object, if the input could be read, or None otherwise.
        """
        import json

        try:
            t = json.load( file )
        except:
            return None

        retVal = ClientParameters()
        for attr in ['s','username','pw','x','v','p','a','A','K_client','u','Y','M1']:
            if attr in t:
                if (attr in ['username','pw']) and (type(t[attr]) is str):
                    setattr( retVal, attr, t[attr] )
                elif type( t[attr] ) is str:
                    setattr( retVal, attr, int(t[attr], 16) )
                elif type( t[attr] ) is int:
                    setattr( retVal, attr, t[attr] )
                else:
                    return None

        return retVal

    def write(self, file) -> bool:
        """
        Write out ClientParameters to a file. pickle makes this a lot easier, but has
          security issues, hence why this method exists.

        PARAMETERS
        ==========
        file: A file-like object to write text to.

        RETURNS
        =======
        True if successful, false otherwise.
        """
        import json

        temp = dict()
        for attr in ['s','username','pw','x','v','p','a','A','K_client','u','Y','M1']:
            value = getattr(self,attr)
            if type(value) in [int,str]:
                temp[attr] = value
            elif type(value) is bytes:
                temp[attr] = value.hex()

        try:
            json.dump( temp, file )
        except:
            return False

        return True



##### METHODS

def split_ip_port( string:str ) -> Optional[tuple[str,int]]:
    """Split the given string into an IP address and port number.
    
    PARAMETERS
    ==========
    string: A string of the form IP:PORT.

    RETURNS
    =======
    If successful, a tuple of the form (IP,PORT), where IP is a 
      string and PORT is a number. Otherwise, returns None.
    """

    assert type(string) == str

    try:
        idx = string.index(':')
        return (string[:idx], int(string[idx+1:]))
    except:
        return None

def int_to_bytes( value:int, length:int ) -> bytes:
    """Convert the given integer into a bytes object with the specified
       number of bytes. Uses network byte order.

    PARAMETERS
    ==========
    value: An int to be converted.
    length: The number of bytes this number occupies.

    RETURNS
    =======
    A bytes object representing the integer.
    """
    
    assert type(value) == int
    assert length > 0   # not necessary, but we're working with positive numbers only

    return value.to_bytes( length, 'big' )

### BEGIN
def i2b( x, l ):    # reminder: type hints are optional!
    """The above, but it passes through bytes objects."""
    if type(x) == int:
        return x.to_bytes( l, 'big' )
    elif type(x) == bytes:
        return x
    else:
        raise Exception(f'Expected an int or bytes, got {type(x)}!')
### END

def bytes_to_int( value:bytes ) -> int:
    """Convert the given bytes object into an integer. Uses network
       byte order.

    PARAMETERS
    ==========
    value: An bytes object to be converted.

    RETURNS
    =======
    An integer representing the bytes object.
    """
    
    assert type(value) == bytes
    return int.from_bytes( value, 'big' )

### BEGIN
def b2i( x ):
    """The above, but it passes through int objects."""
    if type(x) == bytes:
        return int.from_bytes( x, 'big' )
    elif type(x) == int:
        return x
    else:
        raise Exception(f'Expected an int or bytes, got {type(x)}!')

def scr( pw, s, size, n=65_536, r=8, p=1, maxmem=67_118_864 ):
    """A simple wrapper around scrypt to save us from having to repeat the
        same parameters over and over again."""

    pw = pw.encode('utf-8') if type(pw) is str else pw
    return scrypt( pw, salt=s, n=n, r=r, p=p, maxmem=maxmem, dklen=size )

### END

def create_socket( ip:str, port:int, listen:bool=False ) -> Optional[socket.socket]:
    """Create a TCP/IP socket at the specified port, and do the setup
       necessary to turn it into a connecting or receiving socket. Do
       not actually send or receive data here, and do not accept any
       incoming connections!

    PARAMETERS
    ==========
    ip: A string representing the IP address to connect/bind to.
    port: An integer representing the port to connect/bind to.
    listen: A boolean that flags whether or not to set the socket up
       for connecting or receiving.

    RETURNS
    =======
    If successful, a socket object that's been prepared according to 
       the instructions. Otherwise, return None.
    """
    
    assert type(ip) == str
    assert type(port) == int

    # delete this comment and insert your code here
### BEGIN
    sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)

    try:
        if listen:
            sock.bind( (ip, port) )
            sock.listen()
        else:
            sock.connect( (ip, port) )

        return sock
    except:
        return None
### END

def send( sock:socket.socket, data:bytes ) -> int:
    """Send the provided data across the given socket. This is a
       'reliable' send, in the sense that the function retries sending
       until either a) all data has been sent, or b) the socket 
       closes.

    PARAMETERS
    ==========
    sock: A socket object to use for sending and receiving.
    data: A bytes object containing the data to send.

    RETURNS
    =======
    The number of bytes sent. If this value is less than len(data),
       the socket is dead plus an unknown amount of the data was transmitted.
    """
    
    assert type(sock) == socket.socket
    assert type(data) == bytes

    # delete this comment and insert your code here
### BEGIN
    # Yes, this could be made a lot shorter with sendall().
    #  It's still worth showing how to do this properly.
    sent = 0
    while sent < len(data):
        try:
            out = sock.send( data[sent:] )
        except:
            return sent

        if out <= 0:
            return sent
        sent += out

    return sent
### END

def receive( sock:socket.socket, length:int, peek:bool=False ) -> Optional[bytes]:
    """Receive the provided data across the given socket. This function
      operates in two modes. If peek is True, then an attempt to read
      "length" bytes is made with MSG_PEEK flagged. Any bytes read off
      the socket are returned, whether or not they're "length" bytes.
      If peek is False, this function acts as a 'reliable' receive, in 
      the sense that the function never returns until either a) the 
      specified number of bytes was received, or b) the socket closes. 
      Never returning is an option in this mode of operation.
      
      If an exception occurs in peek mode, return None. If not in that 
      mode, return everything read off the socket to date. The callee 
      should treat the socket as dead, in either case.

    PARAMETERS
    ==========
    sock: A socket object to use for sending and receiving.
    length: A positive integer representing the number of bytes to receive.
    peek: If True, read data from the socket buffer but do not remove
      it; if False, read and remove until "length" bytes have been
      retrieved.

    RETURNS
    =======
    Either a bytes object of at most "length" bytes or None, if in peek
      mode. If not, a bytes object containing all data that could be
      received.
    """
    
    assert type(sock) == socket.socket
    assert length > 0

    # delete this comment and insert your code here
### BEGIN
    intake = b''
    while len(intake) < length:

        rem = length - len(intake)
        try:
            if peek:        # easier than special-casing the peek=True case
                return sock.recv( length, socket.MSG_PEEK )
            input = sock.recv( min(rem,4096) )
        except:
            return None if peek else intake

        if input == b'':
            return intake
        intake = intake + input

    return intake

def receive_message( sock:socket.socket, tag_bytes:int=16, message_number:int=None, \
        key:bytes=None ) -> Optional[bytes]:
    """A wrapper which handles receieving a message of unknown length.
      If a key and number is supplied, verify the message and return the contents;
      otherwise, return the raw bytes read off the line. None means an invalid
      message.
    """

    tag = receive( sock, tag_bytes )
    if len(tag) != tag_bytes:
          return None

    len_message_bytes = receive( sock, 1 )
    if len(len_message_bytes) != 1:
          return None

    len_message_raw = receive( sock, len_message_bytes[0] )
    if len(len_message_raw) != len_message_bytes[0]:
          return None
    len_message = int.from_bytes( len_message_raw, 'big' )

    message = receive( sock, len_message )
    if len(message) != len_message:
          return None

    total = tag + len_message_bytes + len_message_raw + message
    if (type(message_number) is int) and (type(key) is bytes):
          return verify_message( total, message_number, key, tag_bytes )
    else:
          return total

### END

def create_message( contents:bytes, message_number:int, key:bytes = b'', tag_bytes:int=32 ) -> bytes:
    """
    Create a message according to the assignment specifications. This involves
      concatenating a tag generated using the message number and (optional) key of the specified
      size, the left-encoded length of the contents, and the contents themselves.

    PARAMETERS
    ==========
    contents: The byte sequence to put inside the message.
    message_number: The sequence number of this message, as an integer.
    key: Use this key to modify the tag, if provided.
    tag_bytes: The size of the tag to use, in bytes.

    RETURNS
    =======
    A byte sequence representing the message.
    """
    assert type(contents) is bytes
    assert type(message_number) is int
    assert message_number >= 0
    assert type(key) is bytes
    assert type(tag_bytes) is int
    assert tag_bytes > 0

    # delete this comment and insert your code here
### BEGIN
    
    msg_len = left_encode( len(contents) )
    return pseudoCSHAKE256( msg_len + contents, tag_bytes<<3, left_encode(message_number) + key, \
            b'CPSC418 MESSAGE TAG' ) + msg_len + contents

### END

def verify_message( message:bytes, message_number:int, key:bytes = b'', tag_bytes:int=32 ) -> Optional[bytes]:
    """
    Reverse the algorithm of create_message(), while also checking the integrity of the message.

    PARAMETERS
    ==========
    contents: The byte sequence to put inside the message.
    message_number: The sequence number of this message, as an integer.
    key: Use this key to modify the tag, if provided.
    tag_bytes: The size of the tag to use, in bytes.

    RETURNS
    =======
    If the message was valid, return the contents of the message; otherwise, return None.
    """
    assert type(message) is bytes
    assert type(message_number) is int
    assert message_number >= 0
    assert type(key) is bytes
    assert type(tag_bytes) is int
    assert tag_bytes > 0

    # delete this comment and insert your code here
### BEGIN

    tag = message[:tag_bytes]
    if tag != pseudoCSHAKE256( message[tag_bytes:], tag_bytes<<3, left_encode(message_number) + key, \
            b'CPSC418 MESSAGE TAG' ):
        return None

    msg_len_bytes = message[tag_bytes]
    msg_len = int.from_bytes( message[tag_bytes+1:tag_bytes+1+msg_len_bytes], 'big' )
    contents = message[tag_bytes+1+msg_len_bytes:]
    
    return None if msg_len != len(contents) else contents

### END


def safe_prime( bits:int, rng:FastCSPRNG, pc:PrimeChecker ) -> int:
    """
    Find a safe prime that's "bits" bits long.

    PARAMETERS
    ==========
    bits: The number of bits the safe prime requires to represent it. Must
      be a positive number.
    rng: A helper object for generating cryptographically-secure randomness.
    pc: A helper for checking if an integer is prime.

    RETURNS
    =======
    A safe prime meeting the above specifications.
    """

    assert bits > 2

    # delete this comment and insert your code here
### BEGIN

    # do a linear search, taking advantage of the fact that all safe primes are congruent to 11 mod 12
    mask = (1 << (bits-1)) - 1                                                          # bitmask only those values we need
    q    = (int.from_bytes(rng.get( (bits+6)>>3 ), 'big') & mask) | (1 << (bits-2))     # guarantee the high bit is set
    q   += 5 - (q % 6)                                                                  # make it 5 (mod 6)

    while True:

        # sieve out some known-bad values before checking primality
        for i,p in enumerate(prime_list):
            test = q % p
            if (test == 0) or (test == (p>>1)):
                break
        else:
            if pc.isprime( q ):
                cand = (q<<1) + 1
                if pc.isprime( cand ):
                    return cand

        q += 6          # ensure q is always 5 (mod 6)

        if q > mask:                # protect against overflow
            q    = (1 << (bits-2)) + 1
            q   += 5 - (q % 6)          # reset this back to where we expect

### END

def prim_root( N:Union[int,bytes] ) -> int:
    """Find a primitive root for N, a large safe prime. Hint: it isn't
       always 2.

    PARAMETERS
    ==========
    N: The prime in question. May be an integer or bytes object.

    RETURNS
    =======
    An integer representing the primitive root. Must be a positive
       number greater than 1.
    """

    # delete this comment and insert your code here
### BEGIN

    N = b2i(N)

    # IMPORTANT: This assumes N is a safe prime. Will fail for other cases!
    group = N-1
    fact  = N>>1      # there's only two prime factors of the group, one of which is 2!
    c     = 1

    # do a linear search, since smaller roots are slightly faster to calculate with
    while c < group:
        c += 1          # offset this to guarantee incrementing before the "continue"s
#        if gcd(N,c) != 1:              # N is prime, so the GCD test is always 1
#            continue
        if pow( c, fact, N ) == 1:
            continue
#        elif pow( c, 2, N ) == 1:       # no need, because only 1 and N-1 could satisfy this
#            continue                    #  and they're excluded from the search range
        else:
            return c

### END


def calc_k( sp:ServerParameters ) -> int:
    """
    Calculate the value of k, according to the assignment specs. You may assume
      every value you need for your calculations exists.

    PARAMETERS
    ==========
    sp: An object containing all the values we need to calculate k.

    RETURNS
    =======
    An integer representing k.
    """
    assert type(sp.N) in [bytes,int]
    assert type(sp.g) in [bytes,int]
    assert type(sp.int_bytes) is int
    assert sp.int_bytes > 0

    # delete this comment and insert your code here
### BEGIN

    k = pseudoCSHAKE256( i2b(sp.g,sp.int_bytes) + i2b(sp.N,sp.int_bytes), \
            sp.int_bytes<<3, S=b'CPSC418 SERVER IDENTITY' )
    return b2i( k ) % b2i( sp.N )             # remember, we want an int!

### END

def calc_x( cp:ClientParameters, sp:ServerParameters ) -> int:
    """
    Calculate the value of x, according to the assignment. You may assume
      every value you need for your calculations exists.

    PARAMETERS
    ==========
    cp: An object containing all the Client-related values we need to calculate x.
    sp: An object containing all the Server-related values we need to calculate x.

    RETURNS
    =======
    An integer representing x.
    """
    assert type(cp.s) == bytes
    assert type(cp.pw) == str
    assert type(sp.int_bytes) is int
    assert sp.int_bytes > 0

    # delete this comment and insert your code here
### BEGIN

    return b2i(scr( cp.pw, i2b(cp.s,sp.salt_bytes), sp.int_bytes ))

### END

def calc_A( cp:ClientParameters, sp:ServerParameters ) -> int:
    """
    Calculate the value of A, according to the assignment. You may assume
      every value you need for your calculations exists.

    PARAMETERS
    ==========
    cp: An object containing all the Client-related values we need to calculate A.
    sp: An object containing all the Server-related values we need to calculate A.

    RETURNS
    =======
    An integer representing A.
    """
    assert type(sp.int_bytes) is int
    assert sp.int_bytes > 0

    # delete this comment and insert your code here
### BEGIN

    # asterix: convert a list/tuple into a list of parameters
    # map: apply a function to each object in a list
    return pow( *map( b2i, [sp.g, cp.a, sp.N] ) )

### END

def calc_B( cp:ClientParameters, sp:ServerParameters ) -> int:
    """
    Calculate the value of B, according to the assignment. You may assume
      every value you need for your calculations exists.

    PARAMETERS
    ==========
    cp: An object containing all the Client-related values we need to calculate B.
    sp: An object containing all the Server-related values we need to calculate B.

    RETURNS
    =======
    An integer representing B.
    """
    assert type(sp.int_bytes) is int
    assert sp.int_bytes > 0

    # delete this comment and insert your code here
### BEGIN

    g, b, N, k, v = map(b2i, [sp.g, sp.b, sp.N, sp.k, cp.v] ) 
    return (pow(g, b, N) - (k*v)) % N

### END

def calc_u( cp:ClientParameters, sp:ServerParameters ) -> int:
    """
    Calculate the value of u, according to the assignment. You may assume
      every value you need for your calculations exists.

    PARAMETERS
    ==========
    cp: An object containing all the Client-related values we need to calculate u.
    sp: An object containing all the Server-related values we need to calculate u.

    RETURNS
    =======
    An integer representing u.
    """
    assert type(sp.int_bytes) is int
    assert sp.int_bytes > 0

    # delete this comment and insert your code here
### BEGIN

    X = i2b(cp.A, sp.int_bytes) + i2b(sp.B, sp.int_bytes)
    u = pseudoCSHAKE256( X, sp.int_bytes<<3, S=b'CPSC418 COMBINED SHARED VALUES' )
    return b2i( u ) % b2i( sp.N )

### END

def calc_K_client( cp:ClientParameters, sp:ServerParameters ) -> int:
    """
    Calculate the value of K_client, according to the assignment. You may assume
      every value you need for your calculations exists.

    PARAMETERS
    ==========
    cp: An object containing all the Client-related values we need to calculate K_client.
    sp: An object containing all the Server-related values we need to calculate K_client.

    RETURNS
    =======
    An integer representing K_client.
    """
    assert type(sp.int_bytes) is int
    assert sp.int_bytes > 0

    # delete this comment and insert your code here
### BEGIN

    B, k, v, a, u, x, N = map( b2i, [sp.B, sp.k, cp.v, cp.a, cp.u, cp.x, sp.N] )
    base     = B + k*v
    exponent = a + u*x
    return pow( base, exponent, N )

### END

def calc_K_server( cp:ClientParameters, sp:ServerParameters ) -> int:
    """
    Calculate the value of K_server, according to the assignment. You may assume
      every value you need for your calculations exists.

    PARAMETERS
    ==========
    cp: An object containing all the Client-related values we need to calculate K_server.
    sp: An object containing all the Server-related values we need to calculate K_server.

    RETURNS
    =======
    An integer representing K_server.
    """
    assert type(sp.int_bytes) is int
    assert sp.int_bytes > 0

    # delete this comment and insert your code here
### BEGIN

    A, v, u, N, b = map( b2i, [cp.A, cp.v, sp.u, sp.N, sp.b] )
    base = (A * pow( v, u, N )) % N
    return pow( base, b, N )

### END

def calc_M1( cp:ClientParameters, sp:ServerParameters ) -> bytes:
    """
    Calculate the value of M1, according to the assignment. You may assume
      every value you need for your calculations exists.

    PARAMETERS
    ==========
    cp: An object containing all the Client-related values we need to calculate M1.
    sp: An object containing all the Server-related values we need to calculate M1.

    RETURNS
    =======
    A bytes object representing M1.
    """
    assert type(sp.int_bytes) is int
    assert sp.int_bytes > 0

    # delete this comment and insert your code here
### BEGIN

    X = i2b( cp.A, sp.int_bytes ) + i2b( cp.Y, sp.int_bytes )
    return pseudoCSHAKE256( X, sp.int_bytes << 3, S=b'CPSC418 CONFIRM KEY' )


def close_sock( sock ):
    """A helper to close sockets cleanly."""
    try:
        sock.shutdown(socket.SHUT_RDWR)
        sock.close()
    except:
        pass
    return None

def varprint( data, label, source="Client" ):
    """A helper for printing out data."""
    global args

    if not (('args' in globals()) and args.verbose):
        return

    if label is not None:
        middle = f"{label} = "
    else:
        middle = ""

    if type(data) == bytes:
        print( f"{source}: Received {middle}<{data.hex()}>" )
    else:
        print( f"{source}: {middle}{data}" )

def parse_left_encode( X: bytes ):
    """
    Extract the value of left_encode(). Returns either a tuple of (int,bytes) or None
      if the int couldn't be decoded.
    """
    if len(X) < 2:
        return (None,X)
    byte_len = X[0]
    if len(X) < 1 + byte_len:
        return (None,X)
    return int.from_bytes( X[1:byte_len+1], 'big' ), X[byte_len+1:]

### END

def client_handshake( sock:socket.socket, sp:ServerParameters ) -> Optional[ServerParameters]:
    """Handle the first message sent from the Server to the Client, from the 
      Client's point of view. This routine also doubles as a setup routine;
      if some values are empty, they get filled in. If some values exist, they
      are checked to ensure they are consistent with stored values. On error,
      the socket must be closed before this function terminates.

    PARAMETERS
    ==========
    sock: A valid socket, connected to the Server.
    sp: An object containing all the Server-related values. This object is 
      not modified by this function! Some values may or may not be present.

    RETURNS
    =======
    If the Server's message could be fully read, and the values it contains
      did not contradict anything already known about the Server, return
      a new copy of the ServerParameters object with any updated information.
      If there was a communication error, or the Server sent conflicting values,
      return None.
    """

    # delete this comment and insert your code here
### BEGIN

    # clone sp, as after this point it may change
    SP = sp.clone()
    SP.message_count = sp.message_count

    # retrieve int_bytes, tag_bytes, salt_bytes, N, and g
    message = receive_message( sock, 16, SP.message_count, b'' )
    if message is None:
        return close_sock( sock )

    # handle the trio of encoded values first
    for attr in ['int_bytes','tag_bytes','salt_bytes']:
        temp, message = parse_left_encode( message )
        if temp is None:
            return close_sock( sock )

        # take advantage of Python's reflection to simplify the code
        if (getattr(SP, attr) is not None) and (getattr(SP, attr) != temp):
            return close_sock( sock )
        elif getattr(SP, attr) is None: 
            setattr(SP, attr, temp)
            varprint( temp, f"SP.{attr}" )

    # then the security parameter pair
    if len(message) != 2 * SP.int_bytes:
        return close_sock( sock )

    if (SP.N is not None) and (i2b( SP.N, SP.int_bytes ) != message[:SP.int_bytes]):
        return close_sock( sock )
    else:
        SP.N = message[:SP.int_bytes]

    if (SP.g is not None) and (i2b( SP.g, SP.int_bytes ) != message[SP.int_bytes:]):
        return close_sock( sock )
    else:
        SP.g = message[SP.int_bytes:]

    varprint( b2i(SP.N), "SP.N" )
    varprint( b2i(SP.g), "SP.g" )

    SP.message_count += 1

    # if we got this far, we must have succeeded
    return SP

### END

def client_register( sock:socket.socket, cp:ClientParameters, sp:ServerParameters, \
        rng:FastCSPRNG ) -> Optional[tuple[ClientParameters,ServerParameters]]:
    """Register the given username with the Server, from the Client. This
      routine doubles as a setup routine, calculating any missing values
      the Client needs to carry out the registration protocol, with two
      notable exceptions: the username and password. If either or both are
      absent, it must immediately error out. On error, close the socket before
      returning. Do not wait for the Server's initial message.

    PARAMETERS
    ==========
    sock: A valid socket, connected to the Server.
    cp: An object containing all the Client-related values. This object is 
      not modified by this function! This object also reflects what the Client
      knows at the given point in time, so some values may or may not be
      present.
    sp: An object containing all the Server-related values. This object is 
      not modified by this function! Like cp, some values may or may not be
      present.
    rng: A helper object for generating cryptographically-secure randomness.

    RETURNS
    =======
    If successful, return a tuple containing versions of (cp, sp) that have
      been modified with new values. If a value can be calculated, it must 
      be calculated. If a necessary value is missing, registration failed, or
      there was a communication error, return None.
    """
    assert type(sp.int_bytes) is int
    assert sp.int_bytes > 0
    assert type(sp.tag_bytes) is int
    assert sp.tag_bytes > 0
    assert type(sp.salt_bytes) is int
    assert sp.salt_bytes > 0
    assert type(sp.N) in [bytes,int]
    assert type(sp.g) in [bytes,int]

    # delete this comment and insert your code here
### BEGIN
    global args         # so we can detect if verbosity is enabled

    # sanity checks on the username and password
    if type(cp.username) is not str:
        if ('args' in globals()) and args.verbose:
            print( "ERROR: Client: client_register: No username was provided!" )
        return None

    if type(cp.pw) is not str:
        if ('args' in globals()) and args.verbose:
            print( "ERROR: Client: client_register: No password was provided!" )
        return None

    varprint( cp.username, "username" )
    varprint( cp.pw, "pw" )

    # clone cp and sp, as after this point they may change
    CP = cp.clone()
    CP.message_count = cp.message_count
    SP = sp.clone()
    SP.message_count = sp.message_count

    # if no salt is present, generate it
    if (type(CP.s) is not bytes) or (len(CP.s) != SP.salt_bytes):
        CP.s = rng.get( SP.salt_bytes )
        CP.x = None     # all of these values depend on the salt,
        CP.v = None     #  thus if we're generating a new salt we know
        CP.p = None     #  that whatever values existed here are invalid

    varprint( '0x' + CP.s.hex(), "s" )

    # we have sufficient information to calculate x, v, and p, so do so
    if type(CP.x) not in [bytes,int]:
        CP.x = calc_x( CP, SP )

    varprint( CP.x, "x" )

    if type(CP.v) not in [bytes,int]:
        CP.v = pow( *map( b2i, [SP.g, CP.x, SP.N] ) )

    varprint( CP.v, "v" )

    if type(CP.p) not in [bytes,int]:
        CP.p = scr( CP.username, CP.s, SP.int_bytes )

    varprint( '0x' + CP.p.hex(), "p" )

    # craft a message to send back
    contents = b'r' + CP.s + i2b(CP.v, SP.int_bytes) + CP.p
    message = create_message( contents, CP.message_count, b'', SP.tag_bytes )

    count = send( sock, message )
    if count != len(message):
        return close_sock( sock )

    # if we made it this far, we succeeded
    CP.message_count += 1
    SP.message_count += 1

    return (CP, SP)

### END

def server_register( sock:socket.socket, sp:ServerParameters, database:dict ) -> \
        Optional[tuple[ServerParameters,dict]]:
    """Handle the Server's side of the registration. This doubles as a setup
      routine, calculating any values which could be calculated and inserting
      new values as they arise. Do not send the Server's initial connection
      message. On error, close the socket before returning.

    PARAMETERS
    ==========
    sock: A socket object that contains the client connection.
    sp: An object containing all the Server-related values. This object is 
      not modified by this function! Some values may or may not be present.
    database: A dictionary mapping all known Client p values (bytes) to a 
      ClientParameters object containing all values the Server knows about.

    RETURNS
    =======
    If the registration process was successful, return an updated version of 
      ServerParameters and the database as a tuple. If it was not, return None. 
      NOTE: a Client that tries to re-register with a different salt and/or 
      password is likely malicious, and should therefore count as an unsuccessful 
      registration.
    """
    assert type(sp.int_bytes) is int
    assert sp.int_bytes > 0
    assert type(sp.tag_bytes) is int
    assert sp.tag_bytes > 0
    assert type(sp.salt_bytes) is int
    assert sp.salt_bytes > 0
    assert type(sp.N) in [bytes,int]
    assert type(sp.g) in [bytes,int]

    # delete this comment and insert your code here
### BEGIN

    # clone the incoming objects, to protect the originals
    SP = sp.clone()
    SP.message_count = sp.message_count
    DATABASE = {key:value.clone() for key,value in database.items()}

    # receive what the Client sent
    message = receive_message( sock, SP.tag_bytes, SP.message_count, b'' )
    if message is None:
        return close_sock( sock )

    # doesn't begin with "r"? error out
    if message[:1] != b'r':
        return close_sock( sock )
    remainder = message[1:]

    # peel off s, v, and p
    if len(remainder) != (SP.salt_bytes + 2*SP.int_bytes):
        return close_sock( sock )

    s = remainder[:SP.salt_bytes]
    varprint( '0x' + s.hex(), 'salt', "Server" )
    remainder = remainder[SP.salt_bytes:]

    v = b2i( remainder[:SP.int_bytes] )
    varprint( v, 'v', "Server" )
    remainder = remainder[SP.int_bytes:]

    p = remainder[:SP.int_bytes]

    # known? Check it matches, being mindful of different data types
    if (p in DATABASE) and ( \
            (b2i(DATABASE[p].s) != b2i(s)) or \
            (b2i(DATABASE[p].v) != b2i(v)) or \
            (b2i(DATABASE[p].p) != b2i(p)) ):
        return close_sock( sock )

    # unknown? Add it
    elif p not in DATABASE:
        temp = ClientParameters()
        temp.s = s
        temp.v = v
        temp.p = p
        temp.message_count = SP.message_count + 1
        DATABASE[p] = temp

    else:
        DATABASE[p].message_count = SP.message_count + 1

    varprint( '0x' + p.hex(), 'p', "Server" )

    # by now we know we've succeeded
    SP.message_count += 1
    return (SP, DATABASE)

### END

def client_key( sock:socket.socket, cp:ClientParameters, sp:ServerParameters, \
        rng:FastCSPRNG ) -> Optional[tuple[ClientParameters,ServerParameters]]:
    """Negotiate a shared key, from the Client's point of view. Calculate any 
      missing values the Client needs, except for those which would have been
      necessary or calculated by registering with the Server. On error, close
      the socket before returning. Do not wait for the Server's initial message.

    PARAMETERS
    ==========
    sock: A valid socket, connected to the Server.
    cp: An object containing all the Client-related values. This object is 
      not modified by this function! This object also reflects what the Client
      knows at the given point in time, so some values may or may not be
      present.
    sp: An object containing all the Server-related values. This object is 
      not modified by this function! Like cp, some values may or may not be
      present.
    rng: A helper object for generating cryptographically-secure randomness.

    RETURNS
    =======
    If successful, return a tuple containing versions of (cp, sp) that have
      been modified with new values. If a value can be calculated, it must 
      be calculated. If a necessary value is missing, registration failed, or
      there was a communication error, return None.
    """
    assert type(sp.int_bytes) is int
    assert sp.int_bytes > 0
    assert type(sp.tag_bytes) is int
    assert sp.tag_bytes > 0
    assert type(sp.salt_bytes) is int
    assert sp.salt_bytes > 0
    assert type(sp.N) in [bytes,int]
    assert type(sp.g) in [bytes,int]

    # delete this comment and insert your code here
### BEGIN

    # clone cp and sp, as after this point they may change
    CP = cp.clone()
    CP.message_count = cp.message_count
    SP = sp.clone()

    # calculate a and A
    CP.a = b2i( rng.get( SP.int_bytes ) )
    while CP.a >= b2i(SP.N):
        CP.a = b2i( rng.get( SP.int_bytes ) )

    CP.A = calc_A( CP, SP )

    varprint( CP.a, 'a' )
    varprint( CP.A, 'A' )

    # send 'k', p, A
    contents = b'k' + b''.join([i2b(x,SP.int_bytes) for x in [CP.p,CP.A]])
    message = create_message( contents, CP.message_count, b'', SP.tag_bytes )

    count = send( sock, message )
    if count != len(message):
        return close_sock( sock )
    CP.message_count += 1

    # receive s, B
    contents = receive_message( sock, SP.tag_bytes, CP.message_count, b'' )
    if contents is None:
        return close_sock( sock )
    CP.message_count += 1

    # verify the length
    if len(contents) != SP.salt_bytes + SP.int_bytes:
        return close_sock( sock )

    # confirm s
    if b2i(CP.s) != b2i( contents[:SP.salt_bytes] ):
        return close_sock( sock )

    SP.B = contents[SP.salt_bytes:]
    varprint( b2i(SP.B), 'B' )

    # calculate u and K_Client
    CP.u        = calc_u( CP, SP )
    CP.K_client = calc_K_client( CP, SP )
    SP.K_server = CP.K_client

    varprint( CP.u, 'u' )
    varprint( CP.K_client, 'K_client' )

    # pick and send Y
    CP.Y = rng.get( SP.int_bytes )
    varprint( '0x' + CP.Y.hex(), 'Y' )

    message = create_message( CP.Y, CP.message_count, i2b(CP.K_client,SP.int_bytes), SP.tag_bytes )

    count = send( sock, message )
    if count != len(message):
        return close_sock( sock )
    CP.message_count += 1

    # receive M1
    contents = receive_message( sock, SP.tag_bytes, CP.message_count, i2b(CP.K_client,SP.int_bytes) )
    if contents is None:
        return close_sock( sock )
    CP.message_count += 1
    SP.message_count = CP.message_count

    # check M1
    test = calc_M1( CP, SP )
    if test != contents:
        return close_sock( sock )
    CP.M1 = test

    varprint( CP.M1, 'M1' )

    # all good? Return the updated objects
    return (CP, SP)

### END

def server_key( sock:socket.socket, sp:ServerParameters, database:dict, \
        rng:FastCSPRNG ) -> Optional[tuple[ServerParameters,dict]]:
    """Negotiate a shared key, from the Server's point of view. Calculate any 
      missing values the Server needs, except for those which would have been
      necessary or calculated by successfully registering a Client. On error, close
      the socket before returning. Do not send the Server's initial connection 
      message, and do not assume the Client has registered. Ignore any prior
      key negotiated for this Client, but once this key's been "confirmed" be
      sure to save a copy for later use.

    PARAMETERS
    ==========
    sock: A socket object that contains the client connection.
    sp: An object containing all the Server-related values. This object is 
      not modified by this function! Some values may or may not be present.
    database: A dictionary mapping all known Client p values (bytes) to 
      ClientParameters objects containing all values the Server knows about.
    rng: A helper object for generating cryptographically-secure randomness.

    RETURNS
    =======
    If successful, return an updated version of sp and the database as a tuple.
      If a value can be calculated, it must be calculated. If a shared key could
      not be negotiated, the Client hasn't registered, or there was a communication 
      failure, return None.
    """
    assert type(sp.int_bytes) is int
    assert sp.int_bytes > 0
    assert type(sp.tag_bytes) is int
    assert sp.tag_bytes > 0
    assert type(sp.salt_bytes) is int
    assert sp.salt_bytes > 0
    assert type(sp.N) in [bytes,int]
    assert type(sp.g) in [bytes,int]

    # delete this comment and insert your code here
### BEGIN

    # clone the incoming objects, to protect the originals
    SP = sp.clone()
    SP.message_count = sp.message_count
    DATABASE = {key:value.clone() for key,value in database.items()}

    # receive 'k', p, A
    contents = receive_message( sock, SP.tag_bytes, SP.message_count, b'' )
    if contents is None:
        return close_sock( sock )
    SP.message_count += 1

    # wrong length? Quit out
    if len(contents) != 1 + 2*SP.int_bytes:
        return close_sock( sock )

    # no 'k'? Quit out
    if contents[:1] != b'k':
        return close_sock( sock )

    p = contents[1:SP.int_bytes+1]
    A = contents[SP.int_bytes+1:]

    varprint( '0x' + p.hex(), 'p', "Server" )
    varprint( b2i(A), 'A', "Server" )

    # p isn't known? Quit out
    if p not in DATABASE:
        return close_sock( sock )

    # retrieve the ClientParameter for the Client and update
    CP = DATABASE[p]
    CP.p = p
    CP.A = A

    # calculate b and B
    SP.b = b2i( rng.get( SP.int_bytes ) )
    while SP.b >= b2i( SP.N ):
        SP.b = b2i( rng.get( SP.int_bytes ) )

    SP.B = calc_B( CP, SP )

    varprint( SP.b, 'b', "Server" )
    varprint( SP.B, 'B', "Server" )
    varprint( '0x' + i2b(CP.s,SP.salt_bytes).hex(), 's', "Server" )

    # send s and B
    contents = i2b(CP.s, SP.salt_bytes) + i2b(SP.B, SP.int_bytes)
    message = create_message( contents, SP.message_count, b'', SP.tag_bytes )

    count = send( sock, message )
    if count != len(message):
        return close_sock( sock )
    SP.message_count += 1

    # calculate u and K_Server
    SP.u        = calc_u( CP, SP )
    SP.K_server = calc_K_server( CP, SP )
    CP.u        = SP.u

    varprint( SP.u, 'u', "Server" )
    varprint( SP.K_server, 'K_server', "Server" )

    # receive Y
    contents = receive_message( sock, SP.tag_bytes, SP.message_count, i2b(SP.K_server,SP.int_bytes) )
    if contents is None:
        return close_sock( sock )
    SP.message_count += 1

    varprint( contents, 'Y', 'Server' )

    # check lengths
    if len(contents) != SP.int_bytes:
        return close_sock( sock )

    SP.Y = contents
    CP.Y = SP.Y

    varprint( '0x' + SP.Y.hex(), 'Y', "Server" )

    # calculate and send M1
    SP.M1 = calc_M1( CP, SP )
    CP.M1 = SP.M1

    varprint( SP.M1, 'M1', "Server" )

    contents = i2b(SP.M1, SP.int_bytes)
    message = create_message( contents, SP.message_count, i2b(SP.K_server,SP.int_bytes), SP.tag_bytes )

    count = send( sock, message )
    if count != len(message):
        return close_sock( sock )
    SP.message_count += 1

    # if we got this far, we must have succeeded
    CP.K_client = SP.K_server
    CP.message_count = SP.message_count
    DATABASE[p] = CP
    return (SP, DATABASE)

### END

def client_file( sock:socket.socket, cp:ClientParameters, sp:ServerParameters, file:bytes ) -> \
        Optional[ClientParameters]:
    """Send a file to the Server, from the Client's point of view. Since this 
      only happens after key negotiation, you can assume any values you need
      to know are present. On error, close the socket before returning. Do not 
      wait for the Server's initial message.

    PARAMETERS
    ==========
    sock: A valid socket, connected to the Server.
    cp: An object containing all the Client-related values. This object is 
      not modified by this function! This object also reflects what the Client
      knows at the given point in time, so some values may or may not be
      present.
    sp: An object containing all the Server-related values. This object is 
      not modified by this function! Like cp, some values may or may not be
      present.
    file: The file to send, as a bytes object.

    RETURNS
    =======
    If the file was successfully transferred, return an updated version of ClientParameters.
      Otherwise, return None.
    """
    assert type(sp.int_bytes) is int
    assert sp.int_bytes > 0
    assert type(sp.tag_bytes) is int
    assert sp.tag_bytes > 0
    assert type(sp.salt_bytes) is int
    assert sp.salt_bytes > 0
    assert type(sp.N) in [bytes,int]
    assert type(sp.g) in [bytes,int]

    # delete this comment and insert your code here
### BEGIN

    # encrypt the file
    cyphertext = MAC_then_encrypt( file, i2b(cp.K_client,sp.int_bytes), sp.salt_bytes<<3, \
            sp.tag_bytes<<3, sp.salt_bytes<<3 )

    # craft a message and send it
    contents = b'f' + i2b(cp.p,sp.int_bytes) + cyphertext
    K_client = i2b( cp.K_client, sp.int_bytes )
    message = create_message( contents, cp.message_count, K_client, sp.tag_bytes )

    count = send( sock, message )
    if count != len(message):
        return close_sock( sock )

    # if we made it here, ClientParameters may have changed
    CP = cp.clone()
    CP.message_count = cp.message_count + 1

    # receive our feedback
    contents = receive_message( sock, sp.tag_bytes, CP.message_count, K_client )
    if contents is None:
        return close_sock( sock )
    CP.message_count += 1

    # figure out if successful 
    success = pseudoCSHAKE256( b's' + K_client + i2b(CP.A,sp.int_bytes) + \
            i2b(CP.Y,sp.int_bytes), 4<<3, S=b'CPSC418 CONFIRM FILE' )

    return CP if contents == success else close_sock(sock)

### END

def server_file( sock:socket.socket, sp:ServerParameters, database:dict ) -> \
        Optional[tuple[ServerParameters,bytes,bytes]]:
    """Receive a file from a Client. Do not assume the Client has registered or
      negotiated a shared key. If they have negotiated a key, you can assume
      all values that need to be calculated have been. On error, close the socket 
      before returning. Do not send the Server's initial connection message.

    PARAMETERS
    ==========
    sock: A socket object that contains the client connection.
    sp: An object containing all the Server-related values. This object is 
      not modified by this function! Some values may or may not be present.
    database: A dictionary mapping all known Client p values (bytes) to 
      ClientParameters objects containing all values the Server knows about.

    RETURNS
    =======
    If successful, return an updated version of sp, plus the username (p) that
      sent the file and the file that was transferred, the latter two as bytes. 
      If a shared key had not been negotiated, the Client hasn't registered, 
      or there was a communication failure, return None.
    """
    assert type(sp.int_bytes) is int
    assert sp.int_bytes > 0
    assert type(sp.tag_bytes) is int
    assert sp.tag_bytes > 0
    assert type(sp.salt_bytes) is int
    assert sp.salt_bytes > 0
    assert type(sp.N) in [bytes,int]
    assert type(sp.g) in [bytes,int]

    # delete this comment and insert your code here
### BEGIN

    # receive the message, but don't verify it (we don't know K_client)
    message = receive_message( sock, sp.tag_bytes, None, None )
    if message is None:
        return close_sock( sock )

    # clone the incoming objects, to protect the originals
    SP = sp.clone()
    SP.message_count = sp.message_count

    # split into tag, length, 'f', p, and file
    tag = message[:SP.tag_bytes]
    content_len, remainder = parse_left_encode( message[SP.tag_bytes:] )

    # might as well verify the mode here
    if remainder[:1] != b'f':
        return close_sock( sock )

    offset = 1
    p = remainder[offset:offset+SP.int_bytes]

    offset += SP.int_bytes
    cyphertext = remainder[offset:]

    # look up p
    if p not in database:
        return close_sock( sock )

    # grab the client key
    CP = database[p]
    if CP.K_client is None:
        return close_sock( sock )

    K_client = i2b( CP.K_client, SP.int_bytes )

    # at long last, we can verify the message
    contents = verify_message( message, SP.message_count, K_client, SP.tag_bytes )
    if contents is None:
        return close_sock( sock )

    # we can finally increment this
    SP.message_count += 1

    # decrypt the file
    file = decrypt_and_verify( cyphertext, K_client, SP.salt_bytes<<3, \
            SP.tag_bytes<<3, SP.salt_bytes<<3 )

    # send back the proper response
    mode = b'f' if file is None else b's'

    contents = pseudoCSHAKE256( mode + K_client + i2b(CP.A,SP.int_bytes) + \
            i2b(CP.Y,SP.int_bytes), 4<<3, S=b'CPSC418 CONFIRM FILE' )
    message = create_message( contents, SP.message_count, K_client, SP.tag_bytes )

    count = send( sock, message )
    if count != len(message):
        return close_sock( sock )
    SP.message_count += 1

    return close_sock(sock) if file is None else (SP,p,file)
    
### END

def write_database( target:Path, database:dict ) -> bool:
    """
    A helper routine to write out the current Client database to disk.

    PARAMETERS
    ==========
    target: A Path object representing a directory to use as persistent storage.
    database: The database to store.

    RETURNS
    =======
    True if successful, False otherwise.
    """

    result = True
    for key,value in database.items():

        output = target / (key.hex() + '.json')
        with output.open('wt') as f:
            result &= value.write(f)

    return result


##### MAIN

if __name__ == '__main__':

    # parse the command line args
    cmdline = argparse.ArgumentParser( description="Test out a secure key exchange algorithm." )

    methods = cmdline.add_argument_group( 'ACTIONS', "The three actions this program can do." )

    methods.add_argument( '--client', action='store_true', \
        help='Perform registration, key negotiation, and file transfer on the given IP address and port.' )
    methods.add_argument( '--send_file', action='store_true', \
        help='Perform registration, key negotiation, and file transfer on the given IP address and port.' )
    methods.add_argument( '--server', action='store_true', \
        help='Launch the Server on the given IP address and port.' )
    methods.add_argument( '--quit', action='store_true', \
        help='Tell the Server on the given IP address and port to quit.' )

    methods = cmdline.add_argument_group( 'OPTIONS', "Modify the defaults used for the above actions." )

    methods.add_argument( '--addr', metavar='IP:PORT', type=str, default="127.0.4.18:3180", \
        help='The IP address and port to connect to.' )
    methods.add_argument( '--username', metavar='NAME', type=str, default="admin", \
        help='The username of the Client.' )
    methods.add_argument( '--password', metavar='PASSWORD', type=str, default="swordfish", \
        help='The password of the Client.' )
    methods.add_argument( '--salt', metavar='HEXADECIMAL', type=lambda x: bytes.fromhex(x), \
        help='The salt of the Client.' )
    methods.add_argument( '--file', metavar='FILE', type=argparse.FileType('rb', 0), \
        help='A file for the Client to transfer over. Randomly generated if not given.' )
    methods.add_argument( '--storage', metavar='PATH', type=Path, \
        help='A directory for the Server to use as persistant storage.' )
    methods.add_argument( '--timeout', metavar='SECONDS', type=int, default=600, \
        help='How long until the program automatically quits. Negative or zero disables this.' )
    methods.add_argument( '--int_bytes', type=int, default=64, \
        help='How many bytes an integer-like value is encoded in, if not already present.' )
    methods.add_argument( '--tag_bytes', type=int, default=16, \
        help='The size of (almost) all tags, in bytes, if not already present.' )
    methods.add_argument( '--salt_bytes', type=int, default=32, \
        help='The size of all salt values, in bytes, if not already present.' )
    methods.add_argument( '-v', '--verbose', action='store_true', \
        help="Be more verbose about what is happening." )

    args = cmdline.parse_args()

    # ensure the number of bits is sane
    if (args.int_bytes < 1) or (args.int_bytes > 512):
        args.int_bytes = 64
    if (args.tag_bytes < 1) or (args.tag_bytes > 512):
        args.tag_bytes = 16
    if (args.salt_bytes < 16) or (args.salt_bytes > 512):
        args.salt_bytes = 32

    # no persistent storage? Use a temp directory to use
    if not args.storage:
        tmpdir = TemporaryDirectory()
        args.storage = Path( tmpdir.name )

    if not args.storage.is_dir():
        print( f'The given persistent storage path, {args.storage.name}, is not a directory. Quitting.' )
        exit(2)

    sp = None
    database = dict()

    # for each file in the directory:
    for file in args.storage.iterdir():

        # skip anything that isn't a JSON file
        if (not file.is_file()) or (file.suffix != '.json'):
            continue

        #  Server.json? It's the Server
        if file.name == 'Server.json':
            with file.open('rt') as f:
                sp = ServerParameters.read(f)

        #  [hexname].json? It's a Client
        else:
            try:
                p = bytes.fromhex( file.stem )
            except:
                continue

            with file.open('rt') as f:
                database[p] = ClientParameters.read(f)

    # no ServerParameters? Generate one
    if sp is None:

        result = split_ip_port( args.addr )
        if result is None:
            print( f'Program: {args.addr} was not a valid IP:port combination. Quitting.')
            exit(1)

        IP, port = result
        sp = ServerParameters( args.int_bytes, args.tag_bytes, args.salt_bytes, IP, port )

    # handle the timeout portion
    killer = None           # save this for later
    if args.timeout > 0:

        # define a handler
        def shutdown( time, verbose=False ):

            sleep( time )
            if verbose:
                print( "Program: exiting after timeout.", flush=True )

            return # optional, but I like having an explicit return

        # launch it
        if args.verbose:
            print( "Program: Launching background timeout.", flush=True )
        killer = Thread( target=shutdown, args=(args.timeout,args.verbose) )
        killer.daemon = True
        killer.start()

    # next off, are we launching the server?
    result      = None     # pre-declare this to allow for cascading
    rng = FastCSPRNG()

    server_proc = None
    if args.server:
        if args.verbose:
            print( "Program: Attempting to launch server.", flush=True )
            print( f"Server: Asked to start on IP {sp.ip} and port {sp.port}.", flush=True )


        if sp.N is None:
            if args.verbose:
                print( f"Server: Generating N, this will take some time.", flush=True )
            prim = PrimeChecker()
            sp.N = safe_prime( sp.int_bytes<<3, rng, prim )
            if args.verbose:
                print( f"Server: Finished generating N.", flush=True )

        # prefer using bytes objects to make server_loop easier
        if type(sp.N) is int:
            sp.N = sp.N.to_bytes( sp.int_bytes, 'big' )

        if sp.g is None:        # this should be quick
            sp.g = prim_root( sp.N )
        if type(sp.g) is int:
            sp.g = sp.g.to_bytes( sp.int_bytes, 'big' )

        sp.k = calc_k( sp )

        # save a persistent copy
        with (args.storage / 'Server.json').open('wt') as f:
            sp.write( f )

        # use an inline routine as this doesn't have to be globally visible
        def server_loop( sp, database, rng, storage, verbose=False ):
            
            # a lemma to help with disconnections
            def disconnect( client, verbose ):
                if verbose:
                    print( f"Server: Closing connection to current Client and waiting for another connection.", flush=True )
                client.shutdown(socket.SHUT_RDWR)
                client.close()

            sock = create_socket( sp.ip, sp.port, listen=True )
            if sock is None:
                if verbose:
                    print( f"Server: Could not create socket, exiting.", flush=True )
                return

            if verbose:
                print( f"Server: Beginning connection loop.", flush=True )
            while True:

                (client, client_address) = sock.accept()
                if verbose:
                    print( f"Server: Got connection from {client_address}.", flush=True )

                # create a copy so Client-specific variables can be easily rolled back
                SP = sp.clone()
                SP.message_count = 0        # reset message count on initial connection

                contents  = b''.join(map( left_encode, [SP.int_bytes,SP.tag_bytes,SP.salt_bytes] ))
                contents += SP.N + SP.g
                message = create_message( contents, SP.message_count, b'', 16 )

                count = send( client, message )
                if count != len(message):
                    disconnect( client, verbose )
                    continue
                SP.message_count += 1

                print( f'Server: Current message count = {SP.message_count} (+1).', flush=True )

                # inner loop: iterate over the incoming messages
                live_connection = True
                while live_connection:

                    print( f'Server: Examining the incoming message from the Client.', flush=True )
                    message = b''
                    target_len = SP.tag_bytes + 1       # tag + number of bytes in length of message
                    retries = 500                       # five seconds is an unreasonable amount of time to wait
                    while (len(message) < target_len) and (retries > 0):
                        message = receive( client, target_len, True )
                        if message == None:             # handle communication errors
                            live_connection = False
                            break

                        retries -= 1
                        sleep( 0.01 )       # insert a delay to avoid chewing up resources

                    if retries <= 0:
                        print( f'Server: Timed out waiting for more data from the Client, closing the connection.', flush=True )
                        break

                    message_length_len = message[-1]
                    target_len += message_length_len + 1 # ... + length of message + mode
                    while len(message) < target_len:
                        message = receive( client, target_len, True )
                        if message == None:
                            live_connection = False
                            break

                        sleep( 0.01 )

                    # now that we know the mode, branch
                    mode = message[-1:]
                    if mode == b'q':
                        print( f'Server: Asked to shut down, closing all connections and preparing to halt.', flush=True )
                        disconnect( client, verbose )
                        sock.shutdown(socket.SHUT_RDWR)
                        sock.close()
                        write_database( storage, database )
                        return

                    elif mode == b'r':
                        if verbose:
                            print( f"Server: Asked to register by Client.", flush=True )

                        old_msgs = SP.message_count
                        temp = server_register( client, SP, database )
                        if (temp is None) or (type(temp) is not tuple) or (len(temp) != 2):
                            if verbose:
                                print( f"Server: Registration failed, closing socket and waiting for another connection.", flush=True )
                            live_connection = False
                            break

                        SP, database = temp
                        print( f'Server: Current message count = {SP.message_count} (+{SP.message_count - old_msgs}).' )
                        if verbose:
                            print( f"Server: Registration complete, current users: {['0x'+x.hex() for x in database]}.", flush=True )

                    elif mode == b'k':
                        if verbose:
                            print( f"Server: Asked to generate shared secret by Client.", flush=True )

                        old_msgs = SP.message_count
                        temp = server_key( client, SP, database, rng )
                        if (temp is None) or (type(temp) is not tuple) or (len(temp) != 2):
                            if verbose:
                                print( f"Server: Secret negotiation failed, closing socket and waiting for another connection.", flush=True )
                            live_connection = False
                            break
                    
                        SP, database = temp
                        print( f'Server: Current message count = {SP.message_count} (+{SP.message_count - old_msgs}).' )
                        if verbose:
                            print( f"Server: Shared key generated: {SP.K_server if type(SP.K_server) is int else SP.K_server.hex()}.", flush=True )

                    elif mode == b'f':
                        if verbose:
                            print( f"Server: Asked to transfer a file by Client.", flush=True )

                        old_msgs = SP.message_count
                        temp = server_file( client, SP, database )
                        if (temp is None) or (type(temp) is not tuple) or (len(temp) != 3):
                            if verbose:
                                print( f"Server: File transfer failed, closing socket and waiting for another connection.", flush=True )
                            live_connection = False
                            break
                    
                        SP, p, file = temp
                        print( f'Server: Current message count = {SP.message_count} (+{SP.message_count - old_msgs}).' )
                        with (storage / (p.hex() + '.bin')).open('wb') as f:
                            f.write( file )

                        if verbose:
                            print( f"Server: File transfer successful, wrote {len(file)} bytes to disk.", flush=True )

                # tidy up after the client disconnects
                if live_connection:
                    if verbose:
                        print( f"Server: Closing connection to Client.", flush=True )
                    disconnect( client, verbose )
                if verbose:
                    print( f"Server: Writing out the database.", flush=True )
                write_database( storage, database )


        # launch the server
        if args.verbose:
            print( "Program: Launching Server.", flush=True )
        server_proc = Thread( target=server_loop, args=(sp, database, rng, args.storage, args.verbose) )
        server_proc.daemon = True
        server_proc.start()

    # finally, check if we're launching the Client
    result      = None     # clean this up

    client_proc = None
    if args.client or args.send_file:
        if args.verbose:
            print( "Program: Attempting to launch Client.", flush=True )
        result = split_ip_port( args.addr )

    if result is not None:

        IP, port = result
        if args.verbose:
            print( f"Client: Asked to connect to IP {IP} and port {port}.", flush=True )

        # another inline routine
        def client_routine( IP, port, cp, sp, rng, verbose=False ):

            sock = create_socket( IP, port, listen=False )
            if sock is None:
                if verbose:
                    print( f"Client: Could not create socket, exiting.", flush=True )
                return

            if verbose:
                print( f"Client: Reading in the Server's handshake.", flush=True )

            result = client_handshake( sock, sp )
            if result is None:
                if verbose:
                    print( f"Client: Failure during handshake phase, exiting.", flush=True )
                return

            sp = result
            cp.message_count += 1      # a side-effect of not passing ClientParameters in
            print( f'Client: Current message count = {cp.message_count} (+1).' )

            if verbose:
                print( f"Client: Performing the registration phase.", flush=True )

            old_msgs = cp.message_count
            results = client_register( sock, cp, sp, rng )
            if (results is None) or (type(results) is not tuple) or (len(results) != 2):
                if verbose:
                    print( f"Client: Registration failed, exiting.", flush=True )
                return

            cp, sp = results
            print( f'Client: Current message count = {cp.message_count} (+{cp.message_count - old_msgs}).' )

            if verbose:
                print( f"Client: Starting to negotiate the shared key.", flush=True )

            old_msgs = cp.message_count
            results = client_key( sock, cp, sp, rng )
            if (results is None) or (type(results) is not tuple) or (len(results) != 2):
                if verbose:
                    print( f"Client: Could not arrive at a shared key.", flush=True )
                return

            cp, sp = results
            print( f'Client: Current message count = {cp.message_count} (+{cp.message_count - old_msgs}).' )

            if verbose:
                print( f'Client: About to send a "file" to the Server.', flush=True )

            old_msgs = cp.message_count
            results = client_file( sock, cp, sp, rng.get( 1 << 19 ) )  # 512kB of random data
            if results is None:
                if verbose:
                    print( f"Client: Could not transmit the file.", flush=True )
                return

            cp = results
            print( f'Client: Current message count = {cp.message_count} (+{cp.message_count - old_msgs}).' )

            # if we made it here, close the socket
            print( f"Client: Transmitted file successfully, ending connection.", flush=True )
            sock.shutdown(socket.SHUT_RDWR)
            sock.close()

            return

        # launch the client
        cp = ClientParameters()
        cp.username = args.username
        cp.pw = args.password
        cp.s = args.salt

        if args.verbose:
            print( "Program: Launching client.", flush=True )
        client_proc = Thread( target=client_routine, args=(IP, port, cp, sp.clone(), rng, args.verbose) )
        client_proc.daemon = True
        client_proc.start()

    # finally, the quitting routine
    result      = None     # clean this up

    if args.quit:
        # defer on the killing portion, in case the client is active
        result = split_ip_port( args.addr )

    if result is not None:

        IP, port = result
        if args.verbose:
            print( f"Quit: Asked to connect to IP {IP} and port {port}.", flush=True )
        if client_proc is not None:
            if args.verbose:
                print( f"Quit: Waiting for the client to complete first.", flush=True )
            client_proc.join()

        if args.verbose:
            print( "Quit: Attempting to kill the server.", flush=True )

        # no need for threading here
        sock = create_socket( IP, port )
        if sock is None:
            if args.verbose:
                print( f"Quit: Could not connect to the server to send the kill signal.", flush=True )

        # handle the handshake
        result = client_handshake( sock, sp.clone() )
        if result is None:
            if args.verbose:
                print( f"Quit: Failure during handshake phase, exiting.", flush=True )
            exit(3)

        SP = result
        content = b'q'
        message = create_message( content, 1, b'', SP.tag_bytes )

        count = send( sock, message )
        if count != len(message):
            if args.verbose:
                print( f"Quit: Socket error when sending the signal.", flush=True )
        elif args.verbose:
                print( f"Quit: Signal sent successfully.", flush=True )

        sock.shutdown(socket.SHUT_RDWR)
        sock.close()

    # finally, we wait until we're told to kill ourselves off, or both the client and server are done
    while not ((server_proc is None) and (client_proc is None)):

        if not killer.is_alive():
            if args.verbose:
                print( f"Program: Timeout reached, so exiting.", flush=True )
            if client_proc is not None:
                client_proc.terminate()
            if server_proc is not None:
                server_proc.terminate()
            exit()

        if (client_proc is not None) and (not client_proc.is_alive()):
            if args.verbose:
                print( f"Program: Client terminated.", flush=True )
            client_proc = None
        
        if (server_proc is not None) and (not server_proc.is_alive()):
            if args.verbose:
                print( f"Program: Server terminated.", flush=True )
            server_proc = None
