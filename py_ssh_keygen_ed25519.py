#! /usr/bin/python
# by pts@fazekas.hu at Thu Dec 15 14:36:25 CET 2016
#
# https://github.com/openssh/openssh-portable/blob/master/PROTOCOL.key
#

import base64
import hashlib  # Needs `easy_install hashlib' on Python 2.4.
import re
import struct
import sys

# --- ed25519 implementation
#
# Based on: https://github.com/pyca/ed25519/blob/master/ed25519.py
#

def get_ed25519_public_key_unsafe(private_key, _bpow=[]):
  """Computes the public key from the private key.

  Not safe to use with secret keys or secret data.
  TODO(pts): Copy-paste why.
  
  Implementation based on:
  https://github.com/pyca/ed25519/blob/master/ed25519.py
  """
  if len(private_key) != 32:
    raise ValueError('Expected private key size: 32.')
  h = hashlib.sha512(private_key).digest()[:32]
  # Constants inlined.
  e = ((1 << 254) | (int(h[::-1].encode('hex'), 16) & ~(7 | 1 << 255))) % (
      (1 << 252) + 0x14def9dea2f79cd65812631a5cf5d3ed)
  q = (1 << 255) - 19
  if not _bpow:
    _bpow.append((
        0x216936d3cd6e53fec0a4e231fdd6dc5c692cc7609525a7b2c9562d608f25d51a,
        0x6666666666666666666666666666666666666666666666666666666666666658, 1,
        0x67875f0fd78b766566ea4e8e64abe37d20f09f80775152f56dde8ab3a5b7dda3))
    for i in xrange(252):  # _bpow[i] == scalarmult(B, 2**i).
      # This is formula sequence 'dbl-2008-hwcd' from
      # http://www.hyperelliptic.org/EFD/g1p/auto-twisted-extended-1.html
      x1, y1, z1, t1 = _bpow[-1]
      a = x1 * x1 % q
      b = y1 * y1 % q
      c = ((z1 * z1) << 1) % q
      hh = -a - b  # dd - b
      ee = ((x1 + y1) * (x1 + y1) + hh) % q
      g = -a + b  # dd + b
      f = g - c
      _bpow.append((ee * f % q, g * hh % q, f * g % q, ee * hh % q))
  x, y, z, t = 0, 1, 1, 0
  for i in xrange(253):
    if e & 1:
      # This is formula sequence 'addition-add-2008-hwcd-3' from
      # http://www.hyperelliptic.org/EFD/g1p/auto-twisted-extended-1.html
      x2, y2, z2, t2 = _bpow[i]
      a = (y - x) * (y2 - x2) % q
      b = (y + x) * (y2 + x2) % q
      c = t * 0xa406d9dc56dffce7198e80f2eef3d13000e0149a8283b156ebd69b9426b2f146 % q * t2 % q
      dd = ((z * z2) << 1) % q
      ee = b - a
      f = dd - c
      g = dd + c
      hh = b + a
      x, y, z, t = (ee * f % q, g * hh % q, f * g % q, ee * hh % q)
    e >>= 1

  def pow2(x, p):
    """== pow(x, 1 << p, q)"""  # TODO(pts): Which one is faster?
    while p > 0:
      x = x * x % q
      p -= 1
    return x

  # z= z^{-1} \mod q$, for z != 0.
  # Adapted from curve25519_athlon.c in djb's Curve25519.
  #z2 = z * z % q
  #z4 = z2 * z2 % q
  #z9 = z4 * z % q
  #z11 = z9 * z2 % q
  #z2_5 = (z11 * z11) % q * z9 % q
  #z2_10 = pow2(z2_5, 5) * z2_5 % q
  #z2_20 = pow2(z2_10, 10) * z2_10 % q
  #z2_40 = pow2(z2_20, 20) * z2_20 % q
  #z2_50 = pow2(z2_40, 10) * z2_10 % q
  #z2_100 = pow2(z2_50, 50) * z2_50 % q
  #z2_200 = pow2(z2_100, 100) * z2_100 % q
  #z2_250 = pow2(z2_200, 50) * z2_50 % q
  #zi = pow2(z2_250, 5) * z11 % q  # 2^255 - 2^5 + 11 = q - 2
  #assert zi == pow(z, pow(2, (q - 2), 57896044618658097711785492504343953926634992332820282019728792003956564819948), q)
  #print z * zi % q
  #assert z * zi % q == 1
  z2 = z * z % q                                # 2
  z9 = pow2(z2, 2) * z % q                      # 9
  z11 = z9 * z2 % q                             # 11
  z2_5_0 = (z11 * z11) % q * z9 % q             # 31 == 2^5 - 2^0
  z2_10_0 = pow2(z2_5_0, 5) * z2_5_0 % q        # 2^10 - 2^0
  z2_20_0 = pow2(z2_10_0, 10) * z2_10_0 % q     # ...
  z2_40_0 = pow2(z2_20_0, 20) * z2_20_0 % q
  z2_50_0 = pow2(z2_40_0, 10) * z2_10_0 % q
  z2_100_0 = pow2(z2_50_0, 50) * z2_50_0 % q
  z2_200_0 = pow2(z2_100_0, 100) * z2_100_0 % q
  z2_250_0 = pow2(z2_200_0, 50) * z2_50_0 % q   # 2^250 - 2^0
  zi = pow2(z2_250_0, 5) * z11 % q            # 2^255 - 2^5 + 11 = q - 2


  x, y = (x * zi) % q, (y * zi) % q
  return ('%064x' % (y & ~(1 << 255) | ((x & 1) << 255))).decode('hex')[::-1]

# ---

def parse_fixed(data, i, size):
  if len(data) < i + size:
    raise ValueError('Too short for parse_fixed.')
  j = i + size
  return j, data[i : j]


def parse_u32(data, i):
  if len(data) < i + 4:
    raise ValueError('Too short for parse_fixed.')
  j = i + 4
  return j, struct.unpack('>L', data[i : j])[0]


def parse_lenu32str(data, i):
  return parse_fixed(data, *parse_u32(data, i))


def parse_openssh_private_key_ed22519(data):
  """Returns (public_key, comment, private_key, checkstr)."""
  if not data.startswith('-----BEGIN OPENSSH PRIVATE KEY-----\n'):
    raise ValueError('Missing OPENSSH PRIVATE KEY.')
  i = data.find('\n')
  j = data.find('-', i + 1)
  if j < 0:
    raise ValueError('Missing end of OPENSSH PRIVATE KEY.')
  try:
    data = base64.b64decode(data[i : j])
  except ValueError:
    raise ValueError('Error in base64.')
  i = 0
  i, magic = parse_fixed(data, i, 15)
  if magic != 'openssh-key-v1\0':
    raise ValueError('Unexpected magic.')
  i, cipher = parse_lenu32str(data, i)
  if cipher != 'none':
    raise ValueError('Expected cipher: none.')
  i, kdf = parse_lenu32str(data, i)
  if kdf != 'none':
    raise ValueError('Expected kdf: none.')
  i, kdfoptions = parse_lenu32str(data, i)
  if kdfoptions:
    raise ValueError('Expected empty kdfoptions.')
  i, key_count = parse_u32(data, i)
  if key_count != 1:
    raise ValueError('Expected key_count: 1')
  i, public_key_desc = parse_lenu32str(data, i)
  j = 0
  j, public_key_type = parse_lenu32str(public_key_desc, j)
  if public_key_type != 'ssh-ed25519':
    raise ValueError('Expected public key type: ssh-ed22519')
  j, public_key = parse_lenu32str(public_key_desc, j)
  if len(public_key) != 32:
    raise ValueError('Expected public key size: 32')
  if j != len(public_key_desc):
    raise ValueError('Public key descriptor too long.')
  i, private_key_desc = parse_lenu32str(data, i)
  if i != len(data):
    raise ValueError('Encoded data too long.')
  if len(private_key_desc) & 7:  # Cipher block size is 8 for 'none'.
    raise ValueError('Private key not padded.')
  j = 0
  j, checkstr1 = parse_fixed(private_key_desc, j, 4)
  j, checkstr2 = parse_fixed(private_key_desc, j, 4)
  if checkstr1 != checkstr2:
    # Any random 4-length string values do.
    raise ValueError('checkint value mismatch.')
  j, private_key_type = parse_lenu32str(private_key_desc, j)
  if private_key_type != 'ssh-ed25519':
    raise ValueError('Expected private key type: ssh-ed22519')
  j, public_key2 = parse_lenu32str(private_key_desc, j)
  if public_key != public_key2:
    raise ValueError('Mismatch in public_key.')
  j, private_key = parse_lenu32str(private_key_desc, j)
  if len(private_key) != 64:
    raise ValueError('Expected private key size: 32')
  if private_key[32:] != public_key:
    raise ValueError('Private key does not match public key.')
  private_key = private_key[:32]
  j, comment = parse_lenu32str(private_key_desc, j)
  if j + 8 <= len(private_key_desc):
    raise ValueError('Private key padding too long.')
  if private_key_desc[j:] != ''.join(
      chr(k) for k in xrange(1, 1 + len(private_key_desc) - j)):
    raise ValueError('Unexpected padding value.')
  if public_key != get_ed25519_public_key_unsafe(private_key):
    raise ValueError('Public key and private key do not match.')
  return public_key, comment, private_key, checkstr1


def build_openssh_private_key_ed22519(public_key, comment, private_key,
                                      checkstr):
  for value in (public_key, comment, private_key, checkstr):
    if not isinstance(value, str):
      raise TypeError
  if len(private_key) == 64:
    if private_key[32:] != public_key:
      raise ValueError('Private key does not match public key.')
    private_key = private_key[:32]
  elif len(private_key) != 32:
    raise ValueError('Expected private key size: 32 or 64')
  if not public_key:
    public_key = get_ed25519_public_key_unsafe(private_key)
    assert len(public_key) == 32
  else:
    if len(public_key) != 32:
      raise ValueError('Expected public key size: 32')
    if public_key != get_ed25519_public_key_unsafe(private_key):
      raise ValueError('Public key and private key do not match.')
  if len(checkstr) != 4:
    raise ValueError('Expected checkstr size: 4')
  # TODO(pts): Check '\r' not in comment and '\n' not in comment (for *.pub).


  data = base64.b64encode(''.join((  # No newlines.
      'openssh-key-v1\0\0\0\0\4none\0\0\0\4none\0\0\0\0\0\0\0\1\0\0\0\x33'
      '\0\0\0\x0bssh-ed25519\0\0\0 ', public_key,
      struct.pack('>L', 131 + len(comment) + (-(len(comment) + 3) & 7)),
      checkstr, checkstr, '\0\0\0\x0bssh-ed25519\0\0\0 ', public_key,
      '\0\0\0@', private_key[:32], public_key, struct.pack('>L', len(comment)),
      comment, '\1\2\3\4\5\6\7'[:-(len(comment) + 3) & 7])))
  output = ['-----BEGIN OPENSSH PRIVATE KEY-----\n']
  for i in xrange(0, len(data), 70):
    output.append(data[i : i + 70])
    output.append('\n')
  output.append('-----END OPENSSH PRIVATE KEY-----\n')
  return ''.join(output)


def parse_openssh_public_key_ed22519(data):
  """Returns (public_key, comment)."""
  data = data.rstrip('\r\n')
  if '\n' in data or '\r' in data:
    raise ValueError('Unexpected newline.')
  try:
    key_type, encoded, comment = data.split(' ', 2)
  except ValueError:
    raise ValueError('Not enough fields.')
  if key_type != 'ssh-ed25519':
    raise ValueError('Expected key type: ssh-ed22519')
  try:
    public_key_desc = base64.b64decode(encoded)
  except ValueError:
    raise ValueError('Error in base64.')
  j = 0
  j, public_key_type = parse_lenu32str(public_key_desc, j)
  if public_key_type != 'ssh-ed25519':
    raise ValueError('Expected public key type: ssh-ed22519')
  j, public_key = parse_lenu32str(public_key_desc, j)
  if len(public_key) != 32:
    raise ValueError('Expected public key size: 32')
  if j != len(public_key_desc):
    raise ValueError('Public key descriptor too long.')
  return public_key, comment


def build_openssh_public_key_ed22519(public_key, comment):
  for value in (public_key, comment):
    if not isinstance(value, str):
      raise TypeError
  if len(public_key) != 32:
    raise ValueError('Expected public key size: 32')
  return 'ssh-ed25519 %s %s\n' % (
      base64.b64encode(''.join(('\0\0\0\x0bssh-ed25519\0\0\0 ', public_key))),
      comment)


def main(argv):
  for filename in argv[1:]:
    if filename.endswith('.pub'):
      continue
    print >>sys.stderr, 'info: trying: %s' % filename

    data = open(filename).read()
    args = parse_openssh_private_key_ed22519(data)
    print args
    data2 = build_openssh_private_key_ed22519(*args)
    if data != data2:
      raise ValueError('Unexpected build private output.')

    data = open(filename + '.pub').read()
    args = parse_openssh_public_key_ed22519(data)
    print args
    data2 = build_openssh_public_key_ed22519(*args)
    if data != data2:
      raise ValueError('Unexpected build public output.')


if __name__ == '__main__':
  sys.exit(main(sys.argv))
