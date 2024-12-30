'''
    libdivide
    =========

    A Python implementation of libdivide.

    This is a way to calculate the factors and do simulated,
    division by multiplication and shifts in Python, which
    has arbitrary-precision integer support.

    This supports both the branchful and branchless algorithms.

    This is obviously not meant for performance but to validate
    our algorithms.

    This is based on [`lidivide`].

    [`libdivide`]: http://libdivide.com/documentation.html
'''

import enum
from dataclasses import dataclass


class Mask(enum.IntEnum):
    '''
    Explanation of the "more" field:

    * Bits 0-5 is the shift value (for shift path or mult path).
    * Bit 6 is the add indicator for mult path.
    * Bit 7 is set if the divisor is negative. We use bit 7 as the negative
      divisor indicator so that we can efficiently use sign extension to
      create a bitmask with all bits set to 1 (if the divisor is negative)
      or 0 (if the divisor is positive).

    u32: [0-4] shift value
         [5] ignored
         [6] add indicator
         magic number of 0 indicates shift path

    s32: [0-4] shift value
         [5] ignored
         [6] add indicator
         [7] indicates negative divisor
         magic number of 0 indicates shift path

    u64: [0-5] shift value
         [6] add indicator
         magic number of 0 indicates shift path

    s64: [0-5] shift value
         [6] add indicator
         [7] indicates negative divisor
         magic number of 0 indicates shift path

    In s32 and s64 branchfree modes, the magic number is negated according to
    whether the divisor is negated. In branchfree strategy, it is not negated.

    Since we want higher-order integers, 6 bits isn't enough (`2^6 == 64`), so
    we migrate our flags over, and change it to a 16-bit more field. So, bit
    14 is always the add indicator, and bit 15 is the negative indicator.
    '''

    SHIFT_16 = 0x1F
    SHIFT_32 = 0x1F
    SHIFT_64 = 0x3F
    SHIFT_128 = 0x7F
    SHIFT_256 = 0xFF
    SHIFT_512 = 0x1FF
    SHIFT_1024 = 0x3FF
    UNIVERSAL = 0x3FFF
    ADD_MARKER = 0x4000
    NEGATIVE_DIVISOR = 0x8000


class Algorithm(enum.IntEnum):
    '''The algorithm type for the division.'''

    SHR = enum.auto()
    FAST = enum.auto()
    GENERAL = enum.auto()


@dataclass
class Divider:
    '''A general-purpose divider.'''

    __slots__ = (
        'bits',
        'divisor',
        'magic',
        'more',
        'algorithm',
        'branchfree',
        'unsigned',
    )

    bits: int
    divisor: int
    magic: int
    more: int
    algorithm: Algorithm
    branchfree: bool
    unsigned: bool

    @classmethod
    def unsigned_gen(cls, bits: int, divisor: int, branchfree: bool = False):
        '''Generate our divider from bits.'''
        if branchfree:
            return unsigned_gen_branchfree(bits, divisor)
        return unsigned_gen_branched(bits, divisor)

    def unsigned_divide(self, numerator: int) -> int:
        '''Do our division and get our quotient.'''
        if self.branchfree:
            return unsigned_divide_branchfree(numerator, self)
        return unsigned_divide_branched(numerator, self)

    def unsigned_divide_remainder(self, numerator: int) -> tuple[int, int]:
        '''Do our division and get our quotient and remainder.'''
        mask = (1 << self.bits) - 1
        quotient = self.unsigned_divide(numerator)
        remainder = numerator - ((self.divisor * quotient) & mask)
        remainder &= mask
        return (quotient, remainder)

    def unsigned_remainder(self, numerator: int) -> int:
        '''Do our division and get our remainder.'''
        return self.unsigned_remainder(numerator)[1]


def leading_zeros(value: int, bits: int) -> int:
    '''Calculate the number of leading zero bits in a value.'''
    fmt = f'{{:0{bits}b}}'
    as_bin = fmt.format(value)
    try:
        return as_bin.index('1')
    except ValueError:
        return bits


def mulhi(x: int, y: int, bits: int) -> int:
    '''Multiply two numbers and extract the high bits of the product.'''
    return (x * y) >> bits


def mullo(x: int, y: int, bits: int) -> int:
    '''Multiply two numbers and extract the low bits of the product.'''
    return (x * y) & ((1 << bits) - 1)


def unsigned_gen_impl(bits: int, divisor: int, branchfree: bool) -> Divider:
    '''
    Generate the multiplications and shifts to emulate a divisor.

    This comprises 3 options:
    1. It's 2^N, so it can be done purely with shifts.
    2. The divisor fits in `e < 2**floor(log2(d))`
    3. We need to use a `bits + 1` general algorithm.

    The last case needs a `2^N / d` factor and requires more bits for the
    calculation than the type size has, so we need a larger factor when
    calculating division coefficients.
    '''

    if divisor == 0:
        raise ZeroDivisionError()
    if divisor > 2**bits or divisor < 1:
        raise ValueError(f'Unsigned value must be in the range [1, {2**bits})')
    floor_log_2_d = bits - 1 - leading_zeros(divisor, bits)

    # power of 2
    if divisor & (divisor - 1) == 0:
        more = floor_log_2_d - branchfree
        return Divider(
            bits=bits,
            divisor=divisor,
            magic=0,
            more=more,
            algorithm=Algorithm.SHR,
            branchfree=branchfree,
            unsigned=True,
        )

    # check fast case, that is, if `e < 2**floor_log_2_d`
    mask = (1 << bits) - 1
    d_power = 1 << (floor_log_2_d + bits)
    proposed_m = int(d_power // divisor)
    rem = int(d_power % divisor)
    e = divisor - rem
    if not branchfree and e < (1 << floor_log_2_d):
        more = floor_log_2_d
        algorithm = Algorithm.FAST
    else:
        # have to use the general bits + 1 algorithm.
        # this expects overflow so we want to mask after
        # each operation to emulate native ops.
        algorithm = Algorithm.GENERAL
        proposed_m = (2 * proposed_m) & mask
        twice_rem = (rem + rem) & mask
        if twice_rem >= divisor or twice_rem < rem:
            proposed_m += 1
            proposed_m &= mask
            more = floor_log_2_d | Mask.ADD_MARKER

    return Divider(
        bits=bits,
        divisor=divisor,
        magic=(1 + proposed_m) & mask,
        more=more,
        algorithm=algorithm,
        branchfree=branchfree,
        unsigned=True,
    )


def unsigned_gen_branched(bits: int, divisor: int) -> Divider:
    '''Generate the multiplications and shifts to emulate a divisor.'''
    return unsigned_gen_impl(bits, divisor, branchfree=False)


def unsigned_gen_branchfree(bits: int, divisor: int) -> Divider:
    '''Generate the multiplications and shifts to emulate a divisor.'''
    divider = unsigned_gen_impl(bits, divisor, branchfree=True)
    divider.more &= Mask.UNIVERSAL
    return divider


def unsigned_divide_branched(numerator: int, divider: Divider) -> int:
    '''
    Do unsigned division with the pre-computed constants.

    This only does division: you must use a multiply and sub to get
    the remainder. This uses a branch to optimize the result, when
    possible.
    '''

    # FIXME: This is branched but validate it
    assert not divider.branchfree
    assert numerator > 0

    if divider.magic == 0:
        return numerator >> divider.more

    # NOTE: Python bitmasks will do wrapping for us too, like a modulo.
    mask = (1 << divider.bits) - 1
    q = mulhi(divider.magic, numerator, divider.bits)
    if (divider.more & Mask.ADD_MARKER) != 0:
        t = (((numerator - 1) & mask) >> 1) + q
        t &= mask
        return t >> (divider.more & Mask.UNIVERSAL)
    else:
        return q >> divider.more


def unsigned_divide_branchfree(numerator: int, divider: Divider) -> int:
    '''
    Do unsigned division with the pre-computed constants.

    This only does division: you must use a multiply and sub to get
    the remainder. This uses a branchless algorithm, which can improve
    performance with branch misses.
    '''

    assert divider.branchfree
    assert numerator > 0

    # NOTE: Python bitmasks will do wrapping for us too, like a modulo.
    mask = (1 << divider.bits) - 1
    q = mulhi(divider.magic, numerator, divider.bits)
    t = (((numerator - 1) & mask) >> 1) + q
    t &= mask

    return t >> divider.more
