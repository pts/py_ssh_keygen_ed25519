#! /usr/bin/python
# by pts@fazekas.hu at Thu Dec 15 14:36:25 CET 2016

""":" #py_ssh_keygen_ed25519: ssh-keygen for ed25519 keypairs.

type python2.7 >/dev/null 2>&1 && exec python2.7 -- "$0" ${1+"$@"}
type python2.6 >/dev/null 2>&1 && exec python2.6 -- "$0" ${1+"$@"}
type python2.5 >/dev/null 2>&1 && exec python2.5 -- "$0" ${1+"$@"}
type python2.4 >/dev/null 2>&1 && exec python2.4 -- "$0" ${1+"$@"}
exec python -- ${1+"$@"}; exit 1

py_ssh_keygen_ed25519 is a command-line tool implemented in Python for
generating unencrypted ed25519 keypairs (public and private keys) to be
used with OpenSSH. It's also a validator for such files.

py_ssh_keygen_ed25519 runs on Python 2.4 (with the external hashlib module
installed), 2.5, 2.6 and 2.7. It doesn't work with Python 3.x. All other
crypto primitives are built in

Usage for keypair generation (as a replacement for ssh-keygen):

  py_ssh_keygen_ed25519.py -t ed25519 -f <outfile> [-C <comment>]

Usage for keypair file verification:

  py_ssh_keygen_ed25519.py --check [<filename> ...]
"""

import base64
import hashlib  # Needs `easy_install hashlib' on Python 2.4.
import os
import re
import struct
import sys

# --- ed25519 implementation
#
# Based on: https://github.com/pyca/ed25519/blob/master/ed25519.py
#

def get_public_key_ed25519_unsafe(private_key, _bpow=[]):
  """Computes the public key from the private key.

  Not safe to use with secret keys or secret data.
  The root of the problem is that Python's long-integer arithmetic is
  not designed for use in cryptography.  Specifically, it may take more
  or less time to execute an operation depending on the values of the
  inputs, and its memory access patterns may also depend on the inputs.
  This opens it to timing and cache side-channel attacks which can
  disclose data to an attacker.  We rely on Python's long-integer
  arithmetic, so we cannot handle secrets without risking their disclosure.

  Implementation based on:
  https://github.com/pyca/ed25519/blob/master/ed25519.py
  """
  if len(private_key) != 32:
    raise ValueError('Expected private key size: 32.')
  h = hashlib.sha512(private_key).digest()[:32]
  # Constants inlined.
  e = ((1 << 254) | (int(h[::-1].encode('hex'), 16) & ~(7 | 1 << 255))) % (
      (1 << 252) + 0x14def9dea2f79cd65812631a5cf5d3ed)
  #ex = ((1 << 254) | (int(h[::-1].encode('hex'), 16) & ~(7 | 1 << 255)))  # !!
  #assert 0, ('%064x' % e).decode('hex')[::-1].encode('hex')
  q = (1 << 255) - 19  # A prime.
  # TODO(pts): Where is basepoint = {9} in curve25519-donna.c hidden below?
  if not _bpow:  # Compute it only for the first time.
    _bpow.append((
        0x216936d3cd6e53fec0a4e231fdd6dc5c692cc7609525a7b2c9562d608f25d51a,
        0x6666666666666666666666666666666666666666666666666666666666666658, 1,
        0x67875f0fd78b766566ea4e8e64abe37d20f09f80775152f56dde8ab3a5b7dda3))
    for i in xrange(252):  # _bpow[i] == scalarmult(B, 2**i).
      # This is formula sequence 'dbl-2008-hwcd' from
      # http://www.hyperelliptic.org/EFD/g1p/auto-twisted-extended-1.html
      x1, y1, z1, t1 = _bpow[-1]
      a, b, c = x1 * x1 % q, y1 * y1 % q, ((z1 * z1) << 1) % q
      hh, g = -a - b, b - a
      ee, f = ((x1 + y1) * (x1 + y1) + hh) % q, g - c
      _bpow.append((ee * f % q, g * hh % q, f * g % q, ee * hh % q))
  x, y, z, t = 0, 1, 1, 0
  m = 0xa406d9dc56dffce7198e80f2eef3d13000e0149a8283b156ebd69b9426b2f146
  for i in xrange(253):
    if e & 1:
      # This is formula sequence 'addition-add-2008-hwcd-3' from
      # http://www.hyperelliptic.org/EFD/g1p/auto-twisted-extended-1.html
      x2, y2, z2, t2 = _bpow[i]
      a, b = (y - x) * (y2 - x2) % q, (y + x) * (y2 + x2) % q
      c, dd = t * m % q * t2 % q, ((z * z2) << 1) % q
      ee, f, g, hh = b - a, dd - c, dd + c, b + a
      x, y, z, t = ee * f % q, g * hh % q, f * g % q, ee * hh % q
    e >>= 1
  zi = pow(z, q - 2, q)  # Modular inverse could be computed 16% faster.
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


def parse_openssh_private_key_ed25519(data):
  """Returns (public_key, comment, private_key, checkstr)."""
  # Based on:
  # https://github.com/openssh/openssh-portable/blob/master/PROTOCOL.key
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
    raise ValueError('Expected public key type: ssh-ed25519')
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
    raise ValueError('Expected private key type: ssh-ed25519')
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
  if '\n' in comment or '\r' in comment:
    # Newline can't be present in the corresponding public key.
    raise ValueError('Comment contains newline.')
  if j + 8 <= len(private_key_desc):
    raise ValueError('Private key padding too long.')
  if private_key_desc[j:] != ''.join(
      chr(k) for k in xrange(1, 1 + len(private_key_desc) - j)):
    raise ValueError('Unexpected padding value.')
  if public_key != get_public_key_ed25519_unsafe(private_key):
    raise ValueError('Public key and private key do not match.')
  return public_key, comment, private_key, checkstr1


def build_openssh_private_key_ed25519(public_key, comment, private_key,
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
    public_key = get_public_key_ed25519_unsafe(private_key)
    assert len(public_key) == 32
  else:
    if len(public_key) != 32:
      raise ValueError('Expected public key size: 32')
    if public_key != get_public_key_ed25519_unsafe(private_key):
      raise ValueError('Public key and private key do not match.')
  if len(checkstr) != 4:
    raise ValueError('Expected checkstr size: 4')
  if '\n' in comment or '\n' in comment:
    # Newline can't be present in the corresponding public key.
    raise ValueError('Comment contains newline.')

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


def parse_openssh_public_key_ed25519(data):
  """Returns (public_key, comment)."""
  data = data.rstrip('\r\n')
  if '\n' in data or '\r' in data:
    raise ValueError('Unexpected newline.')
  try:
    key_type, encoded, comment = data.split(' ', 2)
  except ValueError:
    raise ValueError('Not enough fields.')
  if key_type != 'ssh-ed25519':
    raise ValueError('Expected key type: ssh-ed25519')
  try:
    public_key_desc = base64.b64decode(encoded)
  except ValueError:
    raise ValueError('Error in base64.')
  j = 0
  j, public_key_type = parse_lenu32str(public_key_desc, j)
  if public_key_type != 'ssh-ed25519':
    raise ValueError('Expected public key type: ssh-ed25519')
  j, public_key = parse_lenu32str(public_key_desc, j)
  if len(public_key) != 32:
    raise ValueError('Expected public key size: 32')
  if j != len(public_key_desc):
    raise ValueError('Public key descriptor too long.')
  return public_key, comment


def build_openssh_public_key_ed25519(public_key, comment):
  for value in (public_key, comment):
    if not isinstance(value, str):
      raise TypeError
  if len(public_key) != 32:
    raise ValueError('Expected public key size: 32')
  return 'ssh-ed25519 %s %s\n' % (
      base64.b64encode(''.join(('\0\0\0\x0bssh-ed25519\0\0\0 ', public_key))),
      comment)


def check_keyfiles_ed25519(filename, do_dump=True):
  # !! These keys are (private, public) from: ASCIIHexEncode <tiny_tinyssh_hostkey1/.ed25519.sk
  private_key3 = 'CC9C1BEB99C25449A75CC189DABC78B491C4D7B460A969871FCEB4E1DC1EB952'.decode('hex')
  public_key3 =  '1C0AD6543FE40530F1282BEC3CE6F48F3A028E7BE46A98FE6824860645B9AC19'.decode('hex')
  print private_key3.encode('hex')
  print public_key3.encode('hex')
  print (get_public_key_ed25519_unsafe(private_key3)).encode('hex')

  f = open(filename)
  try:
    private_key_data = f.read()
  finally:
    f.close()
  public_key, comment, private_key, checkstr = (
      parse_openssh_private_key_ed25519(private_key_data))
  print >>sys.stderr, 'info: private key hex: ' + private_key.encode('hex')

  # !!
  items = map(ord, hashlib.sha512(private_key).digest()[:32])
  items[0] &= 248
  items[31] &= 127
  items[31] |= 64
  print >>sys.stderr, 'info: private key hashed hex: ' + (
      ''.join('%02x' % x for x in items))

  print >>sys.stderr, 'info: public  key hex: ' + public_key.encode('hex')
  print >>sys.stderr, 'info: public2 key hex: ' + (get_public_key_ed25519_unsafe(private_key)).encode('hex')
  private_key_data2 = build_openssh_private_key_ed25519(
      public_key, comment, private_key, checkstr)
  if private_key_data != private_key_data2:
    raise ValueError('Unexpected build private output.')

  f = open(filename + '.pub')
  try:
    public_key_data = f.read()
  finally:
    f.close()
  public_key2, comment2 = parse_openssh_public_key_ed25519(
      public_key_data)
  public_key_data2 = build_openssh_public_key_ed25519(
      public_key2, comment2)
  if public_key_data != public_key_data2:
    raise ValueError('Unexpected build public output.')
  if public_key2 != public_key:
    raise ValueError('Public key mismatch in two files.')
  if comment2 != comment:
    raise ValueError('Public key mismatch in two files.')


def check_public_keyfile_ed25519(filename_pub):
  f = open(filename_pub)
  try:
    public_key_data = f.read()
  finally:
    f.close()
  public_key2, comment2 = parse_openssh_public_key_ed25519(
      public_key_data)
  public_key_data2 = build_openssh_public_key_ed25519(
      public_key2, comment2)
  if public_key_data != public_key_data2:
    raise ValueError('Unexpected build public output.')


def generate_random_bytes(size):
  try:
    return os.urandom(size)
  except (OSError, AttributeError, NotImplementedError), e:
    import random
    # `random' isn't cryptographically secure, it's unsafe.
    return ''.join(chr(random.randrange(0, 256)) for _ in xrange(size))


def generate_key_pair_ed25519():
  private_key = generate_random_bytes(32)
  public_key = get_public_key_ed25519_unsafe(private_key)
  return public_key, private_key


class ArgumentError(Exception):
  """Raised when invalid command-line arguments are specified."""


def get_module_docstring():
  return __doc__


def get_doc(doc=None):
  if doc is None:
    doc = get_module_docstring()
  doc = doc.rstrip()
  doc = re.sub(r'\A:"\s*#', '', doc, 1)
  doc = re.sub(r'\n(\ntype python.*)+\nexec python -- .*', '', doc, 1)
  return doc


def main(argv):
  if len(argv) < 2 or argv[1] == '--help':
    print get_doc()
    sys.exit(0)

  if len(argv) > 1 and argv[1] == '--check':
    for filename in argv[2:]:
      if filename.endswith('.pub'):
        print >>sys.stderr, 'info: checking public keyfile: %s' % filename
        check_public_keyfile_ed25519(filename)
      else:
        print >>sys.stderr, 'info: checking keyfiles: %s' % filename
        check_keyfiles_ed25519(filename)
    return

  try:
    filename = comment = key_type = None
    i = 1
    while i < len(argv):
      arg = argv[i]
      i += 1
      if arg == '--':
        break
      if arg == '-' or not arg.startswith('-'):
        i -= 1
        break
      if arg == '-t' and i < len(argv):
        key_type = argv[i]
        i += 1
      elif arg == '-f' and i < len(argv):
        filename = argv[i]
        i += 1
      elif arg == '-C' and i < len(argv):
        comment = argv[i]
        i += 1
      else:
        raise ArgumentError('Unknown flag: %s' % arg)
    if i != len(argv):
      raise ArgumentError('Too many command-line arguments.')
    if key_type is None:
      raise ArgumentError('Please specify: -t ed25519')
    if filename is None:
      raise ArgumentError('Please specify: -f <output-file>')
  except ArgumentError, e:
    print >>sys.stderr, '%s\n\nerror: %s' % (get_doc(), e)
    sys.exit(1)

  if comment is None:
    import getpass
    import socket
    comment = '%s@%s' % (getpass.getuser(), socket.gethostname())
  public_key, private_key = generate_key_pair_ed25519()
  checkstr = generate_random_bytes(4)
  private_key_data = build_openssh_private_key_ed25519(
      public_key, comment, private_key, checkstr)
  # Unlike ssh-keygen, we overwrite files unconditionally.
  try:
    os.remove(filename)
  except OSError, e:
    pass
  f = open(filename, 'wb')
  try:
    os.chmod(filename, 0600)
  except (OSError, AttributeError, NotImplementedError):
    pass
  try:
    f.write(private_key_data)
  finally:
    f.close()
  public_key_data = build_openssh_public_key_ed25519(
      public_key, comment)
  f = open(filename + '.pub', 'wb')
  try:
    f.write(public_key_data)
  finally:
    f.close()
  check_keyfiles_ed25519(filename)  # Just double check.


if __name__ == '__main__':
  sys.exit(main(sys.argv))
