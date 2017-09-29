#! /usr/bin/python
# by pts@fazekas.hu at Fri Sep 29 18:55:20 CEST 2017
#
# Implementation based on:
# https://github.com/pyca/ed25519/blob/master/ed25519.py
#
# Not safe to use with secret keys or secret data.
# The root of the problem is that Python's long-integer arithmetic is
# not designed for use in cryptography.  Specifically, it may take more
# or less time to execute an operation depending on the values of the
# inputs, and its memory access patterns may also depend on the inputs.
# This opens it to timing and cache side-channel attacks which can
# disclose data to an attacker.  We rely on Python's long-integer
# arithmetic, so we cannot handle secrets without risking their disclosure.
#

import hashlib


# !! TODO(pts): Inline hex constants.
q = (1 << 255) - 19
ll = (1 << 252) + 27742317777372353535851937790883648493

#d = -121665 * inv(121666) % q
d = 37095705934669439343138083508754565189542113879843219016388785533085940283555
#I = pow(2, (q - 1) // 4, q)
I = 19681161376707505956807079304988542015446066515923890162744021073123829784752


def xrecover(y):
  xx = (y * y - 1) * pow(d * y * y + 1, q - 2, q)
  x = pow(xx, (q + 3) >> 3, q)
  if (x * x - xx) % q != 0:
    x = (x * I) % q
  if x & 1:
    x = q - x
  return x


#By = 4 * inv(5)
By = 46316835694926478169428394003475163141307993866256225615783033603165251855960
#Bx = xrecover(By)
Bx = 15112221349535400772501151409588531511454012693041857206046113283949847762202
B = (Bx, By, 1, (Bx * By) % q)
del Bx, By


def edwards_add(P, Q):
  # This is formula sequence 'addition-add-2008-hwcd-3' from
  # http://www.hyperelliptic.org/EFD/g1p/auto-twisted-extended-1.html
  (x1, y1, z1, t1) = P
  (x2, y2, z2, t2) = Q

  a = (y1-x1)*(y2-x2) % q
  b = (y1+x1)*(y2+x2) % q
  c = (t1<<1)*d*t2 % q
  dd = (z1<<1)*z2 % q
  e = b - a
  f = dd - c
  g = dd + c
  h = b + a
  x3 = e*f
  y3 = g*h
  t3 = e*h
  z3 = f*g

  return (x3 % q, y3 % q, z3 % q, t3 % q)


def edwards_double(P):
  # This is formula sequence 'dbl-2008-hwcd' from
  # http://www.hyperelliptic.org/EFD/g1p/auto-twisted-extended-1.html
  (x1, y1, z1, t1) = P

  a = x1*x1 % q
  b = y1*y1 % q
  c = (z1<<1)*z1 % q
  # dd = -a
  e = ((x1+y1)*(x1+y1) - a - b) % q
  g = -a + b  # dd + b
  f = g - c
  h = -a - b  # dd - b
  x3 = e*f
  y3 = g*h
  t3 = e*h
  z3 = f*g

  return (x3 % q, y3 % q, z3 % q, t3 % q)


def scalarmult(P, e):
  if e == 0:
    return 0, 1, 1, 0
  Q = scalarmult(P, e >> 1)
  Q = edwards_double(Q)
  if e & 1:
    Q = edwards_add(Q, P)
  return Q


# Bpow[i] == scalarmult(B, 1 << i)
Bpow = []


def make_Bpow():
  P = B
  for i in xrange(253):
    Bpow.append(P)
    P = edwards_double(P)
make_Bpow()


# !! How much faster is this?
def scalarmult_B(e):
  """Implements scalarmult(B, e) more efficiently."""
  # scalarmult(B, l) is the identity.
  e %= ll
  P = 0, 1, 1, 0
  for i in xrange(253):
    if e & 1:
      P = edwards_add(P, Bpow[i])
    e >>= 1
  assert e == 0, e
  return P


def encodepoint(P):
  x, y, z, t = P
  zi = pow(z, q - 2, q)
  x = (x * zi) % q
  y = (y * zi) % q
  bits = [(y >> i) & 1 for i in xrange(255)] + [x & 1]
  return ''.join(
      chr(sum([bits[i * 8 + j] << j for j in xrange(8)]))
      for i in xrange(32))


def publickey_unsafe(sk):
  h = hashlib.sha512(sk).digest()  # 64 bytes.
  a = (1 << 254) + sum((1 << i) * ((ord(h[i >> 3]) >> (i % 8)) & 1) for i in xrange(3, 254))  # !!
  return encodepoint(scalarmult_B(a))


def gint(h):
  assert len(h) in (32, 64)
  #return sum((1 << i) * ((ord(h[i >> 3]) >> (i % 8)) & 1) for i in xrange(512))
  #return sum(((ord(h[i >> 3]) >> (i % 8)) & 1) << i for i in xrange(512))
  #return sum(ord(h[i]) << (i << 3) for i in xrange(64))
  return int(h[::-1].encode('hex'), 16)


def signature_unsafe(m, sk, pk):
  h = hashlib.sha512(sk).digest()  # 64 bytes.
  a = (1 << 254) + sum((1 << i) * ((ord(h[i >> 3]) >> (i % 8)) & 1) for i in xrange(3, 254))  # !!
  # TODO(pts): Compute hash without concatenation.
  r = gint(hashlib.sha512(h[32 : 64] + m).digest())
  R = scalarmult_B(r)
  # TODO(pts): Compute hash without concatenation.
  S = (r + gint(hashlib.sha512(encodepoint(R) + pk + m).digest()) * a) % ll
  return encodepoint(R) + ('%0128x' % S).decode('hex')[:-33:-1]


def verify(s, m, pk):
  if len(s) != 64:
    raise ValueError('Bad signature length.')

  if len(pk) != 32:
    raise ValueError('Bad public key length.')

  def isoncurve(x, y, z, t):
    return (z % q and
        x*y % q == z*t % q and
        (y*y - x*x - z*z - d*t*t) % q == 0)

  def decodepoint(h):
    y = sum((1 << i) * ((ord(h[i >> 3]) >> (i % 8)) & 1) for i in xrange(255))  # !!
    x = xrecover(y)
    if x & 1 != ((ord(h[255 >> 3]) >> (255 % 8)) & 1):  # !!
      x = q - x
    return x, y, 1, (x * y) % q

  R = decodepoint(s[:32])
  if not isoncurve(*R):
    return False
  A = decodepoint(pk)
  if not isoncurve(*A):
    return False
  # TODO(pts): Compute hash without concatenation.
  h = gint(hashlib.sha512(encodepoint(R) + pk + m).digest())

  x1, y1, z1, t1 = P = scalarmult_B(gint(s[32 : 64]))
  x2, y2, z2, t2 = Q = edwards_add(R, scalarmult(A, h))

  return not (not isoncurve(*P) or not isoncurve(*Q) or
     (x1*z2 - x2*z1) % q != 0 or (y1*z2 - y2*z1) % q != 0)


# ---


def check():
  hsk = 'e71fa86cb7a2bfd638ea082ad1f364f8702f49b44009f43f523244a621e4e9b0'.decode('hex')
  hpk = '7df9f38e692271c670530dea40b7bfb08fc07c54ed62998a55d78b9a3f2c6971'.decode('hex')
  usk = '0a137a15eb42116cb7c3cc4727ad6d4d553c2e4a7ec326ea3472f22a42ff44cc'.decode('hex')
  upk = 'd767e033fc0e3df5ebe688e554614068e1e825990dd212939efa26e9f6973e8d'.decode('hex')
  assert hpk == publickey_unsafe(hsk)
  assert upk == publickey_unsafe(usk)
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
    assert s == signature_unsafe(m, sk, pk), which
    assert verify(s, m, pk), which
    assert not verify(xor1(s), m, pk), which
    assert not verify(xor1_32(s), m, pk), which
    assert not verify(s, xor1(m), pk), which
    assert not verify(s, m, xor1(pk)), which
  print 'check OK'


if __name__ == '__main__':
  check()
