#! /usr/bin/python
# by pts@fazekas.hu at Thu Dec 15 14:36:25 CET 2016
#
# https://github.com/openssh/openssh-portable/blob/master/PROTOCOL.key
#

import base64
import struct
import re
import sys


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
  j, comment = parse_lenu32str(private_key_desc, j)
  if j + 8 <= len(private_key_desc):
    raise ValueError('Private key padding too long.')
  if private_key_desc[j:] != ''.join(
      chr(k) for k in xrange(1, 1 + len(private_key_desc) - j)):
    raise ValueError('Unexpected padding value.')
  return public_key, comment, private_key[:32], checkstr1


def build_openssh_private_key_ed22519(public_key, comment, private_key,
                                      checkstr):
  for value in (public_key, comment, private_key, checkstr):
    if not isinstance(value, str):
      raise TypeError
  if len(public_key) != 32:
    raise ValueError('Expected public key size: 32')
  if len(private_key) == 64:
    if private_key[32:] != public_key:
      raise ValueError('Private key does not match public key.')
  elif len(private_key) != 32:
    raise ValueError('Expected private key size: 32 or 64')
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
