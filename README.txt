py_ssh_keygen_ed25519: ssh-keygen for ed25519 keypairs in Pure Python
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
py_ssh_keygen_ed25519 is a command-line tool implemented in Python for
generating unencrypted ed25519 keypairs (public and private keys) to be
used with OpenSSH. It's also a validator for such files.

py_ssh_keygen_ed25519 runs on Python 2.4 (with the external hashlib module
installed), 2.5, 2.6 and 2.7. It doesn't work with Python 3.x. All other
crypto primitives are built in

Usage for keypair generation (as a replacement for ssh-keygen):

  py_ssh_keygen_ed25519.py -t ed2215 -f <outfile> [-C <comment>]

Usage for keypair file verification:

  py_ssh_keygen_ed25519.py --check [<filename> ...]

__END__
