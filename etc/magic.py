'''
    magic
    =====

    Calculate magic numbers for our raw division.

    This algorithm is specialized fore 2^N+1 / 2^N division, which
    differs significantly from our own implementation goals.
'''

import math


def is_valid(x, div_bits, num_bits):
    '''Determine if the power is valid.'''
    small_max = 2**div_bits - 1
    large_max = 2**num_bits - 1
    return (
        x <= small_max
        and (large_max / (x**2)) < x
    )


def choose_multiplier(divisor, bits, is_signed=False):
    '''
    Choose multiplier algorithm from:
        https://gmplib.org/~tege/divcnst-pldi94.pdf
    '''

    # Precision is the number of bits of precision we need,
    # which for signed values, even in 1's/2's complement, is
    # 1 less than the bits.
    precision = bits
    if is_signed:
        precision -= 1

    div_bits = math.ceil(math.log2(divisor))
    sh_post = div_bits
    m_low = 2**(bits+div_bits) // divisor
    m_high = (2**(bits+div_bits) + 2**(bits + div_bits - precision)) // divisor

    while m_low // 2 < m_high // 2 and sh_post > 0:
        m_low //= 2
        m_high //= 2
        sh_post -= 1

    return (m_high, sh_post, div_bits)


def fast_shift(divisor):
    '''
    Check if we can do a fast shift for quick division as a smaller type.
    This only holds if the divisor is not rounded while shifting.
    '''

    n = 0
    while divisor % 2**(n + 1) == 0:
        n += 1
    return n


def is_pow2(value):
    '''Determine if the value is an exact power-of-two.'''
    return value == 2**int(math.log2(value))


def calculate_factors(d, num_bits, div_bits):
    '''Print the divisor constants for a single divisor.'''

    fast_shr = fast_shift(d)
    factor, factor_shr, d_bits = choose_multiplier(d, num_bits)

    if factor >= 2**num_bits:
        # Cannot fit in numerator bits, must revert to the slow algorithm.
        raise NotImplementedError('TODO')
    elif fast_shr != 0:
        fast = 1 << (div_bits + fast_shr)
        return (fast, fast_shr, factor, factor_shr)
    else:
        raise NotImplementedError('TODO')


def fast_divrem(num, den, fast, fast_shr, factor, factor_shr, num_bits, div_bits):  # noqa
    '''Fast divrem optimization if we can.'''
    div_mask = 2**div_bits - 1
    num_mask = 2**num_bits - 1
    if num < fast:
        quot = int(((num >> fast_shr) & div_mask) // (den >> fast_shr))
    else:
        quot = mulhi(num, factor, div_bits) >> factor_shr
    rem = (num - ((quot * den) & num_mask)) & div_mask
    return (quot, rem)


def mulhi(x, y, half_bits):
    '''Multiply two values and get our upper bits.'''
    # NOTE: These values should be the same size
    y_mask = 2**half_bits - 1
    x0 = x & y_mask
    x1 = (x >> half_bits) & y_mask

    y0 = y & y_mask
    y1 = (y >> half_bits) & y_mask

    w0 = (x0 * y0) & y_mask
    m = (((x0 * y1) & y_mask) + (w0 >> half_bits) & y_mask)
    w1 = m & y_mask
    w2 = (m >> half_bits) & y_mask
    w3 = ((x1 * y0 + w1) >> half_bits) & y_mask

    p0 = (x1 * y1) & y_mask
    p1 = (p0 + w2) & y_mask
    p2 = (p1 + w3) & y_mask
    return p2
