import struct


def d2n(data, size):
    number = len(data) // size
    if size == 1:
        format = "<" + "B" * number
    elif size == 2:
        format = "<" + "H" * number
    elif size == 4:
        format = "<" + "I" * number
    elif size == 8:
        format = "<" + "Q" * number
    else:
        raise ValueError("Size of data invalid")
    return struct.unpack(format, data)

def n2d(number, size):
    if size == 1:
        format = "<" + "B"
    elif size == 2:
        format = "<" + "H"
    elif size == 4:
        format = "<" + "I"
    elif size == 8:
        format = "<" + "Q"
    else:
        raise ValueError("Size of data invalid")
    return struct.pack(format, number)