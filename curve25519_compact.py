#! /usr/bin/python
#
# Implementation based on:
# https://github.com/nnathan/eccsnacks/blob/master/eccsnacks/curve25519.py
# , which is based on: https://tools.ietf.org/html/rfc7748
#
# Implementation equivalent to curve25519-donna.c
#
# Similar implementation with classes:
# https://github.com/openalias/dnscrypt-python/blob/master/slownacl/curve25519.py
#

__all__ = ['scalarmult', 'scalarmult_base']

# implementation is a translation of the pseudocode
# specified in RFC7748: https://tools.ietf.org/html/rfc7748

P = 2 ** 255 - 19
A24 = 121665


def cswap(swap, x_2, x_3):
    dummy = swap * ((x_2 - x_3) % P)
    x_2 = x_2 - dummy
    x_2 %= P
    x_3 = x_3 + dummy
    x_3 %= P
    return (x_2, x_3)


def X25519(k, u):
    x_1 = u
    x_2 = 1
    z_2 = 0
    x_3 = u
    z_3 = 1
    swap = 0

    for t in reversed(xrange(255)):
        k_t = (k >> t) & 1
        swap ^= k_t
        x_2, x_3 = cswap(swap, x_2, x_3)
        z_2, z_3 = cswap(swap, z_2, z_3)
        swap = k_t

        A = x_2 + z_2
        A %= P

        AA = A * A
        AA %= P

        B = x_2 - z_2
        B %= P

        BB = B * B
        BB %= P

        E = AA - BB
        E %= P

        C = x_3 + z_3
        C %= P

        D = x_3 - z_3
        D %= P

        DA = D * A
        DA %= P

        CB = C * B
        CB %= P

        x_3 = ((DA + CB) % P)**2
        x_3 %= P

        z_3 = x_1 * (((DA - CB) % P)**2) % P
        z_3 %= P

        x_2 = AA * BB
        x_2 %= P

        z_2 = E * ((AA + (A24 * E) % P) % P)
        z_2 %= P

    x_2, x_3 = cswap(swap, x_2, x_3)
    z_2, z_3 = cswap(swap, z_2, z_3)

    return (x_2 * pow(z_2, P - 2, P)) % P


# Equivalent to RFC7748 decodeUCoordinate followed by decodeLittleEndian
def unpack(s):
    if len(s) != 32:
        raise ValueError('Invalid Curve25519 scalar (len=%d)' % len(s))
    t = sum(ord(s[i]) << (8 * i) for i in range(31))
    t += ((ord(s[31]) & 0x7f) << 248)
    return t


def pack(n):
    return ''.join([chr((n >> (8 * i)) & 255) for i in range(32)])


def clamp(n):
    n &= ~7
    n &= ~(128 << 8 * 31)
    n |= 64 << 8 * 31
    return n


def scalarmult(n, p):
    '''
       Expects n and p in the form as 32-byte strings.

       Multiplies group element p by integer n. Returns the resulting group
       element as 32-byte string.
    '''

    n = clamp(unpack(n))
    p = unpack(p)
    return pack(X25519(n, p))


def scalarmult_base(n):
    '''
       Expects n in the form as 32-byte string.

       Computes scalar product of standard group element (9) and n.
       Returns the resulting group element as 32-byte string.
    '''

    n = clamp(unpack(n))
    return pack(X25519(n, 9))


def check():
  # Test vector is from tinyssh source code:
  # crypto-tests/crypto_scalarmult_curve25519test.c
  basepoint = '0900000000000000000000000000000000000000000000000000000000000000'.decode('hex')
  d = '562c1eb5fdb28129bd37495835d4b1307ddb573880121742f713f1056769d5bf'.decode('hex')
  r = 'f9c3dac2104c80b252d0aeec377afd5d1ef2c8c348c29e12ddb2d0c8b198ff7f'.decode('hex')

  # The order matters, scalarmult is not commutative.
  assert scalarmult(d, basepoint) == r
  assert scalarmult_base(d) == r
  print 'check OK'


if __name__ == '__main__':
  check()
