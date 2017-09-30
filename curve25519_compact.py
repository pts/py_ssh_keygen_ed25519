#! /usr/bin/python
# by pts@fazekas.hu at Sat Sep 30 03:17:14 CEST 2017

"""curve25519_compact.py: Compact Curve25519 crypto DH library.

This is a compact implementation of the elliptic curve Diffie--Hellman key
exchange (kex) crpyto using the elliptic curve Curve25519, in pure
Python 2.x. It works with Python 2.4, 2.5, 2.6 and 2.7 out of the box, and it
doesn't use any non-standard Python modules.

This implementation is relatively fast, as fast as compact pure Python code
can get.

This is not safe to use with secret keys or secret data.
The root of the problem is that Python's long-integer arithmetic is
not designed for use in cryptography.  Specifically, it may take more
or less time to execute an operation depending on the values of the
inputs, and its memory access patterns may also depend on the inputs.
This opens it to timing and cache side-channel attacks which can
disclose data to an attacker.  We rely on Python's long-integer
arithmetic, so we cannot handle secrets without risking their disclosure.

The public API is the scalarmult function. Calling scalarmult with 1
argument only (instead of 2) is equivalent to scalarmult_base in other APIs.

Here is how to use it for Diffie--Hellman key exchange:

* Alice generates a 32-byte random string ask and computes
  apk := scalarmult(ask).
* Bob generates a 32-byte random string bsk and computes
  bpk := scalarmult(bsk).
* Alice sends apk to Bob.
* Bob sends bpk to Alice.
* Alice computes ak := scalarmult(ask, bpk), 32 bytes.
* Bob computes bk := scalarmult(bsk, apk), 32 bytes.
* Now ak == bk, and Alice and Bob have this 32-byte shared secret, which Eve
  (the eavesdropper) doesn't know.

This implements all crypto primitives needed by the Diffie-Hellman key
exchange between ssh and sshd for
``KexAlgorithms curve25519-sha256@libssh.org''.

With ``HostKeyAlgorithms ssh-ed25519'' and ssh-ed25519 user keys, ssh and
sshd use elliptic curve signature generation and verification using the
curve ed25519, implemented in ed25519_compact.py instead.
Despite the name similarity and the same key size (32 bytes), Curve25519
and ed25519 don't share behavior, test vectors or code.

Implementation based on:
https://github.com/nnathan/eccsnacks/blob/master/eccsnacks/curve25519.py
, which is based on: https://tools.ietf.org/html/rfc7748

Implementation eqiuvalent to curve25519-donna.c

Similar implementation with classes:
https://github.com/openalias/dnscrypt-python/blob/master/slownacl/curve25519.py
"""

def scalarmult(n, p=None):
  # n is a group element string, p is a string representing an integer. Both
  # are 32 bytes.
  if len(n) != 32:
    raise ValueError('Invalid Curve25519 n.')
  if p is None:
    u = 9
  else:
    if len(p) != 32:
      raise ValueError('Invalid Curve25519 p.')
    u = int(p[::-1].encode('hex'), 16)
  k = (int(n[::-1].encode('hex'), 16) & ~(1 << 255 | 7)) | 1 << 254
  ql, x1, x2, z2, x3, z3, do_swap = 2 ** 255 - 19, u, 1, 0, u, 1, 0
  for t in xrange(254, -1, -1):
    kt = (k >> t) & 1
    if do_swap ^ kt:
      x2, x3, z2, z3 = x3, x2, z3, z2
    do_swap = kt
    a, b = (x2 + z2) % ql, (x2 - z2) % ql
    aa, bb = (a * a) % ql, (b * b) % ql
    c, d = (x3 + z3) % ql, (x3 - z3) % ql
    da, cb = d * a % ql, c * b % ql
    d1, d2 = da + cb, da - cb
    x3, z3 = d1 * d1 % ql, x1 * d2 * d2 % ql
    x2, e = aa * bb % ql, (aa - bb) % ql
    z2 = e * (aa + 121665 * e) % ql
  if do_swap:
    x2, x3, z2, z3 = x3, x2, z3, z2
  return ('%064x' % ((x2 * pow(z2, ql - 2, ql)) % ql)).decode('hex')[::-1]


def check():
  # Test vector is from tinyssh source code:
  # crypto-tests/crypto_scalarmult_curve25519test.c
  basepoint = '0900000000000000000000000000000000000000000000000000000000000000'.decode('hex')
  d = '562c1eb5fdb28129bd37495835d4b1307ddb573880121742f713f1056769d5bf'.decode('hex')
  r = 'f9c3dac2104c80b252d0aeec377afd5d1ef2c8c348c29e12ddb2d0c8b198ff7f'.decode('hex')

  # The order matters, scalarmult is not commutative.
  assert scalarmult(d, basepoint) == r
  assert scalarmult(d) == r

  # Diffie--Hellman key exchange.
  ask, bsk = '\xab' + '\xcd' * 31, '\x12' + '\x34' * 31
  apk, bpk = scalarmult(ask), scalarmult(bsk)
  assert apk != bpk
  assert scalarmult(ask, bpk) == scalarmult(bsk, apk)
  assert scalarmult(ask, bpk) != scalarmult(bsk, '\00' + apk[1:])
  assert len(scalarmult(ask, bpk)) == 32

  print 'check OK'


if __name__ == '__main__':
  check()
