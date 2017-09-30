#! /usr/bin/python
# by pts@fazekas.hu at Fri Sep 29 18:55:20 CEST 2017

"""ed25519_compact.py: Compact ed25519 crypto signing library.

This is a compact implementation of the signing and signature verification
operations of ed25519 elliptic curve asymmetric (public key) crypto, in pure
Python 2.x. It works with Python 2.5, 2.6 and 2.7 out of the box, and it
works with Python 2.4 if the hashlib package is installed from pypi. It
doesn't use any non-standard Python modules (except for hashlib in Python
2.4).

This implementation is relatively fast, as fast as compact pure Python code
can get.

The public API is the publickey, sign and verify functions.

This implements crypto all primitives needed by ssh and sshd (except for key
exchange):

* ssh-keygen uses publickey(...) to generate the server host keypair
* ssh-keygen uses publickey(...) to generate the user keypair
* sshd uses sign(...) with the server host secret key
* ssh uses verify(...) with the server host public key
* ssh uses sign(...) with the user secret key
* sshd uses verify(...) with the user public key

Sizes and generation:

* secret key: 32 bytes (can be any random value)
* public key: 32 bytes (generated from the secret key deterministically)
* signature: 64 bytes (genereated from the secret key and the message
  deterministically)

This is not safe to use with secret keys or secret data.
The root of the problem is that Python's long-integer arithmetic is
not designed for use in cryptography.  Specifically, it may take more
or less time to execute an operation depending on the values of the
inputs, and its memory access patterns may also depend on the inputs.
This opens it to timing and cache side-channel attacks which can
disclose data to an attacker.  We rely on Python's long-integer
arithmetic, so we cannot handle secrets without risking their disclosure.

Implementation based on:
https://github.com/pyca/ed25519/blob/master/ed25519.py
, which is based on
http://ed25519.cr.yp.to/python/ed25519.py
"""

import hashlib


def _edwards_add(p, q):
  dl = 0x52036cee2b6ffe738cc740797779e89800700a4d4141d8ab75eb4dca135978a3
  ql = (1 << 255) - 19
  x1, y1, z1, t1 = p
  x2, y2, z2, t2 = q
  a, b = (y1 - x1) * (y2 - x2) % ql, (y1 + x1) * (y2 + x2) % ql
  c, d = (t1 << 1) * dl * t2 % ql, (z1 << 1) * z2 % ql
  e, f, g, h = b - a, d - c, d + c, b + a
  return e * f % ql, g * h % ql, f * g % ql, e * h % ql


def _edwards_double(p):
  ql = (1 << 255) - 19
  x1, y1, z1, t1 = p
  a, b, c = x1 * x1 % ql, y1 * y1 % ql, (z1 << 1) * z1 % ql
  e, g, h = ((x1 + y1) * (x1 + y1) - a - b) % ql, b - a, -b - a
  f = g - c
  return e * f % ql, g * h % ql, f * g % ql, e * h % ql


def _hash3(a, b, c):
  h = hashlib.sha512(a)
  h.update(b)
  h.update(c)
  return h.digest()


def _scalarmult(p, e):
  q, j = (0, 1, 1, 0), 1
  while j <= e:
    j <<= 1
  while j > 1:
    j >>= 1
    q = _edwards_double(q)
    if e & j:
      q = _edwards_add(q, p)
  return q


def _scalarmult_b(e, _bpow=[(bx, by, 1, (bx * by) % ((1 << 255) - 19))
    for bx, by in
    ((0x216936d3cd6e53fec0a4e231fdd6dc5c692cc7609525a7b2c9562d608f25d51a,
     (1 << 256) // 5 * 2 - 14),)]):
  # Implements _scalarmult(b, e) more efficiently, with an overall speed
  # increase of about 1.374 (27.22% faster).
  e %= (1 << 252) | 0x14def9dea2f79cd65812631a5cf5d3ed
  p = 0, 1, 1, 0
  for i in xrange(253):
    if len(_bpow) <= i:
      # _bpow[i] == _scalarmult(b, 1 << i).
      _bpow[i:] = [_edwards_double(_bpow[i - 1])]
    if e & (1 << i):
      p = _edwards_add(p, _bpow[i])
  return p
del bx, by  # !! Remove all constants.


def publickey(sk):
  """Generate a public key from the specified secret key."""
  #if len(sk) != 32:  # Typical is 32, but we don't check.
  x, y, z, t = _scalarmult_b((1 << 254) |
      (int(_hash3(sk, '', '')[:32][::-1].encode('hex'), 16) & ~(7 | 1 << 255)))
  ql = (1 << 255) - 19
  zi = pow(z, ql - 2, ql)
  x, y = (x * zi) % ql, (y * zi) % ql
  return ('%064x' % (y | (x & 1) << 255)).decode('hex')[::-1]


def sign(m, sk, pk=None):
  """Sign the specified message using a secret key."""
  #if len(sk) != 32:  # Typical is 32, but we don't check.
  if not pk:
    pk = publickey(sk)
  if len(pk) != 32:
    raise ValueError('Bad public key length.')
  h = _hash3(sk, '', '')  # 64 bytes.
  r = int(_hash3(h[32 : 64], m, '')[::-1].encode('hex'), 16)
  x, y, z, t = _scalarmult_b(r)
  ql = (1 << 255) - 19
  zi = pow(z, ql - 2, ql)
  x, y = (x * zi) % ql, (y * zi) % ql
  p = ('%064x' % (y | (x & 1) << 255)).decode('hex')[::-1]
  return p + ('%064x' % ((r + int(_hash3(p, pk, m)[::-1]
      .encode('hex'), 16) * ((1 << 254) | (int(h[:32][::-1].encode('hex'), 16) &
       ~(7 | 1 << 255)))) % ((1 << 252) | 0x14def9dea2f79cd65812631a5cf5d3ed))
       ).decode('hex')[:-33:-1]


def verify(s, m, pk):
  """Verify message signature using a public key.

  Invariant: verify(sign(m, sk), m, publickey(sk)) is true for any m and sk.
  """
  if len(s) != 64:
    raise ValueError('Bad signature length.')
  if len(pk) != 32:
    raise ValueError('Bad public key length.')
  dl = 0x52036cee2b6ffe738cc740797779e89800700a4d4141d8ab75eb4dca135978a3
  ql = (1 << 255) - 19

  def isoncurve(x, y, z, t):
    return (z % ql and
        x * y % ql == z * t % ql and
        (y * y - x * x - z * z - dl * t * t) % ql == 0)

  def decodepoint(y):
    y1 = (y >> 255) & 1
    y &= ~(1 << 255)
    yy = y * y % ql
    xx = (yy - 1) * pow(dl * yy + 1, ql - 2, ql)
    x = pow(xx, (ql + 3) >> 3, ql)
    if (x * x - xx) % ql != 0:
      x = (x *
        0x2b8324804fc1df0b2b4d00993dfbd7a72f431806ad2fe478c4ee1b274a0ea0b0) % ql
    if x & 1:
      x = ql - x
    if x & 1 != y1:
      x = ql - x
    return x, y, 1, (x * y) % ql

  r = decodepoint(int(s[:32][::-1].encode('hex'), 16))
  if not isoncurve(*r):
    return False
  a = decodepoint(int(pk[::-1].encode('hex'), 16))
  if not isoncurve(*a):
    return False
  x1, y1, z1, t1 = p = _scalarmult_b(int(s[32 : 64][::-1].encode('hex'), 16))
  x2, y2, z2, t2 = q = _edwards_add(r, _scalarmult(a, int(_hash3(
      s[:32], pk, m)[::-1].encode('hex'), 16)))
  return bool(isoncurve(*p) and isoncurve(*q) and
     (x1 * z2 - x2 * z1) % ql == 0 and (y1 * z2 - y2 * z1) % ql == 0)


def check():
  hsk = 'e71fa86cb7a2bfd638ea082ad1f364f8702f49b44009f43f523244a621e4e9b0'.decode('hex')
  hpk = '7df9f38e692271c670530dea40b7bfb08fc07c54ed62998a55d78b9a3f2c6971'.decode('hex')
  usk = '0a137a15eb42116cb7c3cc4727ad6d4d553c2e4a7ec326ea3472f22a42ff44cc'.decode('hex')
  upk = 'd767e033fc0e3df5ebe688e554614068e1e825990dd212939efa26e9f6973e8d'.decode('hex')
  assert len(hpk) == len(upk) == 32
  assert hpk == publickey(hsk)
  assert upk == publickey(usk)
  def xor1(s):  # Returns s with the s[0] xored with '\1'.
    assert s
    return chr(ord(s[0]) ^ 1) + s[1:]
  def xor1_32(s):  # Returns s with the s[32] xored with '\1'.
    assert len(s) > 32
    return s[:32] + chr(ord(s[32]) ^ 1) + s[33:]
  for which, m, s, sk, pk in (
      ('a', 'cf32122409544fd680c272ea2756a5fe37d0b0c8a11d092f1bfa4720f7ac3993'.decode('hex'), 'a12bf2f69c555868561b592a677e227eb31622d4a4bc7b6efaf677720c1a61c6159ae7906ee16777fda64bfd024a80d5bc8cb7d534abe033669d10352c3def08'.decode('hex'), hsk, hpk),
      ('b', 'cdcdeee839089f79fb969a298c0f7dc35ff091556b9bb4b5e4726ad49ac73ec3'.decode('hex'), 'cd74452de0885b833b948060277660ddd4b9635fc4e785f5bc7180202759514c3f587e5b7c18ebcb442325e7f2c451b7876874b04139b5a854edf77b69037404'.decode('hex'), hsk, hpk),
      ('c', '00000020cf32122409544fd680c272ea2756a5fe37d0b0c8a11d092f1bfa4720f7ac39933200000004707473380000000e7373682d636f6e6e656374696f6e000000097075626c69636b6579010000000b7373682d65643235353139000000330000000b7373682d6564323535313900000020d767e033fc0e3df5ebe688e554614068e1e825990dd212939efa26e9f6973e8d'.decode('hex'), '92828b0e28ae91e25f7e8db64228a925378ba5137831ee7220355037ea02568a3de3de03f4301a5e29338e04f34c9e77b7af7958acdcdc15762d8334e02c0000'.decode('hex'), usk, upk),
      ('d', '00000020cdcdeee839089f79fb969a298c0f7dc35ff091556b9bb4b5e4726ad49ac73ec33200000004707473380000000e7373682d636f6e6e656374696f6e000000097075626c69636b6579010000000b7373682d65643235353139000000330000000b7373682d6564323535313900000020d767e033fc0e3df5ebe688e554614068e1e825990dd212939efa26e9f6973e8d'.decode('hex'), '408343d3abf46daaa6112b5e8ca6d9e238343090816cf40bc8370aaa73936995ad2db80373fd66fa87f2a2338a3a3220bdcdde3c4dc3e4137c5d45177eec360b'.decode('hex'), usk, upk),
      ):
    assert len(s) == 64
    assert s == sign(m, sk, pk), which
    assert s == sign(m, sk), which
    assert verify(s, m, pk), which
    assert not verify(xor1(s), m, pk), which
    assert not verify(xor1_32(s), m, pk), which
    assert not verify(s, xor1(m), pk), which
    assert not verify(s, m, xor1(pk)), which
  print 'check OK'


if __name__ == '__main__':
  check()
