#!/usr/bin/env python3

##### IMPORTS

import argparse

from collections.abc import Callable

import bz2
import csv
from datetime import date, timedelta
from hashlib import shake_256
from multiprocessing import Pool
import numpy as np
from os import cpu_count

from sys import exit, stdout

from time import time_ns
from typing import Iterator, Mapping, Optional, Union

# add any additional modules you need here
### BEGIN
from secrets import token_bytes
### END

##### METHODS

def generate_iv( length:int ) -> bytes:
    """
    Generate an initialization vector for encryption. Must be drawn from a
       cryptographically-secure pseudo-random number generator.

    PARAMETERS
    ==========
    length: The length of the IV desired, in bytes.

    RETURNS
    =======
    A bytes object containing the IV.
    """
    assert type(length) is int

# delete this comment and insert your code here
### BEGIN

    return token_bytes( length )

### END

def xor( a:bytes, b:bytes ) -> bytes:
    """
    Bit-wise exclusive-or two byte sequences. If the two bytes objects differ in
       length, pad with zeros.

    PARAMETERS
    ==========
    a, b: bytes objects to be XORed together.

    RETURNS
    =======
    A bytes object containing the results.
    """
    assert type(a) is bytes
    assert type(b) is bytes

# delete this comment and insert your code here
### BEGIN

    # ensure a is shorter than b
    if len(a) > len(b):
        temp = a
        a = b
        b = temp

    result = bytearray(b)       # take advantage of implicit zero padding
    for i, x in enumerate(a):
        result[i] ^= x          # XOR the matching bytes, ignore the rest
    return bytes(result)        # convert back to an immutable bytes object

    # exercise: can you accomplish all this in three lines?

### END

def left_encode( x:int ) -> bytes:
    """
    Unambiguously encode a number into a sequence of bytes, as defined by
      NIST Special Publication 800-185. In English, the algorithm generates
      a byte encoding of the number, where the most-significant bit of the
      number is at the start of the first byte and the least-significant bit
      of the number is at the end of last byte. It then prepends the number
      of bytes in the encoding, itself encoded as a byte.

    PARAMETERS
    ==========
    x: An integer to encode. Must be positive or zero, and less than a very
      large number.

    RETURNS
    =======
    A sequence of bytes encoding the number.
    """
    assert type(x) is int
    assert 0 <= x <= (1 << 2040)

# delete this comment and insert your code here
### BEGIN

    len_bytes = max( 1, (x.bit_length() + 7) >> 3 )
    return len_bytes.to_bytes(1,'big') + x.to_bytes(len_bytes,'big')

### END

def bytepad( X:bytes, w:int ) -> bytes:
    """
    Unambiguously pad a binary sequence with zeros until it is a multiple of "w"
      bytes long, as defined by NIST Special Publication 800-185. In English, the 
      algorithm prepends the sequence with left_encode(w), then pads the entire
      sequence with bits until it an appropriate length. NIST's original definition
      states that "X" is a bit stream, but those aren't well supported in Python,
      so we'll work exclusively in bytes.

    PARAMETERS
    ==========
    X: A sequence of bytes that may need padding.
    w: The output byte sequence is w * n bytes long, where "n" is an integer
      greater than or equal to one.

    RETURNS
    =======
    A sequence of bytes that is a multiple of "w" bytes long.
    """
    assert type(X) is bytes
    assert type(w) is int
    assert w > 0

# delete this comment and insert your code here
### BEGIN

    z = left_encode(w) + X
    return z + bytes( (-len(z)) % w )

### END

def encode_string( S:Union[bytes,str] ) -> bytes:
    """
    Unambiguously encode a sequence of bits, as defined by NIST Special 
      Publication 800-185. In English, the algorithm uses left_encode() to 
      prepend the length of the bit stream to it. As Python does not have
      good support for bit sequences, we'll use bytes sequences instead.
      For programmer convenience, we'll also accept strings as input and
      automatically encode them into a byte sequence with UTF-8.

    PARAMETERS
    ==========
    S: Either a string or sequence of bytes to be encoded.

    RETURNS
    =======
    A sequence of bytes that has been encoded according to the algorithm.
    """
    assert type(S) in [bytes,str]

# delete this comment and insert your code here
### BEGIN

    if type(S) is str:
        S = S.encode('utf-8')
    return left_encode( len(S)<<3 ) + S

### END

def pseudoCSHAKE256( X:Union[bytes,str], L:int=1088, N:Union[bytes,str]=b"", \
        S:Union[bytes,str]=b"" ) -> bytes:
    """
    Implement a variant of the cSHAKE256 algorithm, as defined by NIST Special 
      Publication 800-185. In English, the original algorithm encodes N and S, 
      concatenates them, and pads the result until it is a multiple of 136 bytes 
      long. It prepends that result to X and appends a zero bit, then passes that 
      to the Keccak[512] algorithm with a request for it to return L bits. That 
      output is then returned. As Python does not have good support for bit sequences,
      we'll use byte sequences instead. For ease of use, we'll also accept
      strings and automatically encode them to byte sequences via UTF-8.

      We'll substitute hashlib's shake_256 for Keccak[512], which is identical 
      except for an inability to handle bit sequences. As a consequnce we cannot 
      append a zero bit as the official cSHAKE256 spec demands; for this implementation, 
      append a zero byte instead. That one change is why this is "pseudoCSHAKE256".

    PARAMETERS
    ==========
    X: Either a string or sequence of bytes to be hashed.
    L: The number of bits to return, as an integer. Since we don't support bit
      sequences, this MUST be a multiple of eight.
    N: Either a string or sequence of bytes, which is used to define other 
      hash functions.
    S: Either a string or sequence of bytes, which is used to customize the output
      of pseudoCSHAKE256.

    RETURNS
    =======
    The hash value of the input, as a sequence of bytes.
    """
    assert type(X) in [bytes,str]
    assert L >= 0
    assert (L & 0x7) == 0       # we can only deliver byte-resolution output
    assert type(N) in [bytes,str]
    assert type(S) in [bytes,str]

# delete this comment and insert your code here
### BEGIN

    X, N, S = [v.encode('utf-8') if type(v) is str else v for v in [X,N,S]]

    if (N == b'') and (S == b''):   # converting N and S makes this easier to code
        return shake_256( X ).digest(L >> 3)

    prefix = bytepad( encode_string(N) + encode_string(S), 136 )
    return shake_256( prefix + X + b'\x00' ).digest(L >> 3)

### END

def encrypt( iv:bytes, plaintext:Union[bytes,str], enc_key:bytes ) -> bytes:
    """
    Encrypt the given plaintext, with the given IV and key, using pseudoCSHAKE256().
      In English, this algorithm generates a random byte stream by hashing the
      concatenation of the encoded iv string and encoded encryption key string, 
      in that order, asking for a digest exactly as long as the plaintext. That 
      digest is XOR-ed with the plaintext to give the encrypted output.
         
    Do not prepend the IV to the output. Customize pseudoCSHAKE256() by supplying
      the byte sequence "ENCRYPT", and use the length of the binary plaintext 
      stream in bits for N, after encoding it with left_encode(). The lack 
      of a matching decrypt() function is deliberate.

    PARAMETERS
    ==========
    iv:        The initialization vector used to boost semantic security, a byte sequence.
    plaintext: The data to be encrypted, which could either be a byte sequence or string.
    enc_key:   A bytes object to be used as an encryption key.

    RETURNS
    =======
    A bytes object containing the encrypted value. Note that the return is not a list or
      generator.
    """
    assert type(iv) is bytes
    assert type(plaintext) in [bytes,str]
    assert type(enc_key) is bytes

# delete this comment and insert your code here
### BEGIN

    if type(plaintext) is str:
        plaintext = plaintext.encode('utf-8')

    input = encode_string(iv) + encode_string(enc_key)
    randomness = pseudoCSHAKE256( input, len(plaintext)<<3, \
            left_encode( len(plaintext)<<3 ), b'ENCRYPT' )
    return xor( plaintext, randomness )

### END


def MAC_then_encrypt( plaintext:Union[bytes,str], key:Union[bytes,str], \
        iv_bits:int=256, tag_bits:int=128, key_bits:int=128 ) -> bytes:
    """
    Encrypt a plaintext with your encryption function. In English, this algorithm
      uses encode_string() to encode the plaintext. It calculates a tag of the 
      encoded plaintext via pseudoCSHAKE256 (customized with the bytes "TAG"), 
      derives the actual encryption key from the iv via pseudoCSHAKE256 (N is 
      the user-supplied key, S is the byte sequence "KEY_DERIVATION"). It then 
      uses encrypt() to encrypt the concatenation of the tag and encoded plaintext 
      with the derived key, and returns the output but with the IV prepended 
      to it.

    The output must be decryptable by decrypt_and_verify(). Note the order of 
      operations!
    
    PARAMETERS
    ==========
    plaintext: The bytes or string object to be encrypted. Not necessarily padded!
    key: The bytes or string object to be used as a key.
    iv_bits: The length of the desired IV, in bits. Must be greater than 256
      and a multiple of 8.
    key_bits: The length of the generated key, in bits. Must be greater than 128
      and a multiple of 8.
    tag_bits: The length of the tag, in bits. Must be positive and a multiple 
      of 8.

    RETURNS
    =======
    The full cyphertext, as a bytes object. Note that the return is not a list or
      generator.
    """
    assert type(plaintext) in [bytes,str]
    assert type(key) in [bytes,str]
    assert iv_bits >= 256
    assert (iv_bits & 0x7) == 0
    assert tag_bits > 0
    assert (tag_bits & 0x7) == 0
    assert key_bits >= 128
    assert (key_bits & 0x7) == 0

# delete this comment and insert your code here
### BEGIN

    to_enc  = encode_string(plaintext)
    tag     = pseudoCSHAKE256( to_enc, tag_bits, S=b'TAG' )
    iv      = generate_iv( iv_bits>>3 )
    enc_key = pseudoCSHAKE256( iv, key_bits, N=key, S=b'KEY_DERIVATION' )
    cypher  = encrypt( iv, tag + to_enc, enc_key )

    return iv + cypher

### END

def decrypt_and_verify( cyphertext:bytes, key:Union[bytes,str], \
        iv_bits:int=256, tag_bits:int=128, key_bits:int=128 ) -> bytes:
    """
    Decrypt a plaintext that had been encrypted with MAC_then_encrypt().
      Also performs integrity checking to help ensure the original wasn't
      corrupted.
    
    PARAMETERS
    ==========
    cyphertext: The bytes object to be decrypted.
    key: The bytes or string object to be used as a key.
    iv_bits: The length of the desired IV, in bits. Must be greater than 256
      and a multiple of 8.
    key_bits: The length of the generated key, in bits. Must be greater than 128
      and a multiple of 8.
    tag_bits: The length of the tag, in bits. Must be positive and a multiple 
      of 8.

    RETURNS
    =======
    If the cyphertext could be decrypted and is valid, this returns a bytes 
      object containing the plaintext. Otherwise, it returns None.
    """
    assert type(cyphertext) is bytes
    assert len(cyphertext) >= (iv_bits + tag_bits)>>3 + 2
    assert type(key) in [bytes,str]
    assert iv_bits >= 256
    assert (iv_bits & 0x7) == 0
    assert tag_bits > 0
    assert (tag_bits & 0x7) == 0
    assert key_bits >= 128
    assert (key_bits & 0x7) == 0

# delete this comment and insert your code here
### BEGIN

    iv_bytes = iv_bits >> 3
    tag_bytes = tag_bits >> 3

    iv      = cyphertext[:iv_bytes]
    enc_key = pseudoCSHAKE256( iv, key_bits, N=key, S=b'KEY_DERIVATION' )
    combo   = encrypt( iv, cyphertext[iv_bytes:], enc_key )
    mac     = combo[:tag_bytes]

    if mac != pseudoCSHAKE256( combo[tag_bytes:], tag_bits, S=b'TAG' ):
        return None

    len_bytes         = combo[tag_bytes]
    length            = int.from_bytes( combo[tag_bytes+1:tag_bytes+1+len_bytes], 'big' ) >> 3
    plaintext         = combo[tag_bytes+1+len_bytes:]

    return plaintext if len(plaintext) == length else None

### END

def generate_passwords( start_date:date, end_date:date, names:dict ):
    """
    A generator that creates all the passwords we'd use for a brute-force attack.
      A valid password comes in the form NAME + YEAR + MONTH + DAY, where
      "NAME" is a name drawn from the "names" dictionary, and YEAR, MONTH, and
      DAY are the respective integers converted to strings. 

    Each of the four components are optional, but at least one must be present 
      and the order of concatenation is constant. MONTH and DAY values can either 
      be a direct conversion, or one that's been padded to always be two characters
      by prepending a "0". YEAR can either be four characters, or the last two 
      digits of the year with zero-padding. NAME is always all-caps. No separators
      are used to deliniate between components. Any remaining details are on
      the assignment specification.

    An old but still relevant tutorial on generators: https://wiki.python.org/moin/Generators

    PARAMETERS
    ==========
    start_date: The earliest possible date that could be used for a password, as
      a date object.
    end_date: The latest possible date that could be used for a password, as
      a date object. Note that this value could be output!
    names: A dictionary object containing three lists of equal length. The one
      keyed to 'First name at birth' is a list of first names assigned at birth.
      'VALUE' is the total number of Canadians assigned that first name for the 
      given year, and 'REF_DATE' contains the year those statistics were gathered.

    RETURNS
    =======
    None.

    YIELDS
    =======
    A potential password as a string, according to the above specifications.
    """
    assert type(start_date) is date
    assert type(end_date) is date
    assert type(names) is dict
    for key in ['REF_DATE','First name at birth','VALUE']:
        assert key in names
        assert len(names['REF_DATE']) == len(names[key])

# delete this comment and insert your code here
### BEGIN

    # build up the date side of things, date-only answers first
    dates = set()
    for offset in range((end_date - start_date).days + 1):
        current = start_date + timedelta(offset)
        for year in [f'{current.year}',f'{current.year%100:02d}']:
            dates.add( year )
            for month in [f'{current.month}',f'{current.month:02d}']:
                dates.add( month )
                dates.add( year + month )
                for day in [f'{current.day}',f'{current.day:02d}']:
                    dates.add( day )
                    dates.add( year + day )
                    dates.add( month + day )
                    dates.add( year + month + day )

    # yield all the date answers immediately
    for d in dates:
        yield d

    # still going? convolve those dates with names
    freq = dict()
    for i,n in enumerate(names['First name at birth']):
        if n in freq:
            freq[n] += names['VALUE'][i]
        else:
            freq[n] = names['VALUE'][i]

    # sort the names from most to least popular, to up the odds of discovery
    ordered = sorted( freq.keys(), key=lambda x:freq[x], reverse=True )
    for name in ordered:
        yield name
        for d in dates:
            yield name.upper() + d

### END

def load_names( input ):
    """
    Load the name database from disk, and format for use with generate_passwords().
      The canonical database is a BZ2-compressed CSV file, with at least four
      columns: 'REF_DATE' (the year the stats were gathered), 'First name at birth'
      (a first name in all-caps), 'Indicator' (the type of statistic stored in
      'VALUE') and 'VALUE (the value of the 'Indicator'). The original source
      of this CSV file is this Statistics Canada dataset:

    https://www150.statcan.gc.ca/t1/tbl1/en/tv.action?pid=1710014701

    PARAMETERS
    ==========
    input: A File-like object for accessing the database.

    RETURNS
    =======
    A dictionary object with three equal-length lists under the keys 'REF_DATE',
      'First name at birth', and 'VALUE'.
    """

    # set up some storage space
    names = {col:[] for col in ['REF_DATE','First name at birth','VALUE']}

    # parse the database
    with bz2.open(input,'rt') as file:
        for row in csv.DictReader(file):

            # we only care about the number of people born with a name
            if row['Indicator'] == 'Frequency':
                for col in ['REF_DATE','First name at birth','VALUE']:
                    names[col].append( row[col] )

    # convert some of the columns to more relevant values
    names['REF_DATE'] = [int(x) for x in names['REF_DATE']]
    names['VALUE'] = [int(float(x)) for x in names['VALUE']]
    
    return names


##### MAIN


if __name__ == '__main__':

    # parse the command line args
    cmdline = argparse.ArgumentParser( description="Encrypt or decrypt a file." )

    methods = cmdline.add_argument_group( 'ACTIONS', "The three actions this program can do." )

    methods.add_argument( '--decrypt', metavar='FILE', type=argparse.FileType('rb', 0), \
        help='A file to be decrypted.' )
    methods.add_argument( '--encrypt', metavar='FILE', type=argparse.FileType('rb', 0), \
        help='A file to be encrypted.' )
    methods.add_argument( '--dump', action='store_true', \
        help='Dump the passwords this program would check in brute-force mode.' )

    methods = cmdline.add_argument_group( 'OPTIONS', "Modify the defaults used for the above actions." )

    methods.add_argument( '--output', metavar='OUTPUT', type=argparse.FileType('wb', 0), \
        help='The output file. If omitted, print the decrypted plaintext or dump to stdout. The destination\'s contents are wiped, even on error.' )
    methods.add_argument( '--password', metavar='PASSWORD', type=str, default="swordfish", \
        help='The password to use as a key.' )
    methods.add_argument( '--reference', metavar='FILE', type=argparse.FileType('rb', 0), \
        help='If provided, check the output matches what is in this file.' )
    methods.add_argument( '--threads', type=int, default=0, \
        help='Number of threads to use when brute-forcing the password. Numbers < 1 implies all available.' )

    methods.add_argument( '--start_date', type=date.fromisoformat, default=date(2003,1,1), \
        help='When brute-forcing passwords, start from this date (inclusive).' )
    methods.add_argument( '--end_date', type=date.fromisoformat, default=date(2006,12,31), \
        help='When brute-forcing passwords, end on this date (inclusive).' )
    methods.add_argument( '--names', metavar='FILE', type=argparse.FileType('rb', 0), \
        help='If provided, use this name list to brute-force the password.' )

    methods.add_argument( '--iv_bytes', type=int, default=32, \
        help='The number of bytes to use for the initialization vector. Must be a positive integer greater than 31.' )
    methods.add_argument( '--key_bytes', type=int, default=16, \
        help='The number of bytes to use for the derived key. Must be a positive integer greater than 15.' )
    methods.add_argument( '--tag_bytes', type=int, default=16, \
        help='The number of bytes to use for the tag. Must be a positive integer greater than 0.' )

    args = cmdline.parse_args()

    if args.threads < 1:
        args.threads = cpu_count()

    if args.iv_bytes < 32:
        args.iv_bytes = 32
    if args.key_bytes < 16:
        args.key_bytes = 16
    if args.tag_bytes < 1:
        args.tag_bytes = 1

    # which mode are we in?
    if args.decrypt:

        plaintext = None
        cyphertext = args.decrypt.read()
        args.decrypt.close()

        if args.names:
            
            names = load_names( args.names )
            
            def check_password( x ):
                retVal = decrypt_and_verify( cyphertext, x, args.iv_bytes<<3, args.tag_bytes<<3, args.key_bytes<<3 )
                return (retVal,x) if retVal else None

            if args.threads > 1:
                with Pool(args.threads) as p:
                    for output in p.imap( check_password, generate_passwords(args.start_date, args.end_date, names), 32 ):
                        if output:
                            plaintext, password = output
                            print( f'Found the password for this file: {password}' )
                            break
            else:
                for output in map( check_password, generate_passwords(args.start_date, args.end_date, names)):
                    if output:
                        plaintext, password = output
                        print( f'Found the password for this file: {password}' )
                        break

        else:
            plaintext = decrypt_and_verify( cyphertext, args.password, args.iv_bytes<<3, args.tag_bytes<<3, args.key_bytes<<3 )

        if plaintext is None:
            print( "ERROR: Could not decrypt the file!" )
            exit( 1 )

        if args.reference:
            ref = args.reference.read()
            if ref != plaintext:
                print( "ERROR: The output and reference did not match!" )
                exit( 2 )

        if args.output:
            args.output.write( plaintext )
            args.output.close()

        else:
            try:
                print( plaintext.decode('utf-8') )
            except UnicodeError as e:
                print( "WARNING: Could not print out the encrypted contents. Was it UTF-8 encoded?" )
                exit( 3 )

    elif args.encrypt:

        cyphertext = MAC_then_encrypt( args.encrypt.read(), args.password, args.iv_bytes<<3, args.tag_bytes<<3, args.key_bytes<<3 )

        if args.reference:
            ref = args.reference.read()
            if ref != cyphertext:
                print( "ERROR: The output and reference did not match!" )
                exit( 4 )

        if args.output:
            args.output.write( cyphertext )
            args.output.close()

        else:
            print( "As the cyphertext is binary, it will not be printed to stdout." )

    elif args.dump and args.names:

        names = load_names( args.names )
        for password in generate_passwords(args.start_date, args.end_date, names):
            if args.output:
                args.output.write( password.encode('utf-8') + b'\n' )
            else:
                stdout.buffer.write( password.encode('utf-8') + b'\n' )

    else:

        print( "Please select one of encryption, decryption, or dumping." )
