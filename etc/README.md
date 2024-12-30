# Other Algorithms

## Libdivide

This has the logic for [libdivide](https://github.com/ridiculousfish/libdivide) provided as Python code, which provides same-width division optimization, that is 64-bit over 64-bit, etc. Although this is much faster for scalar types, in practice, it's slightly faster than Knuth division for large numerators with mid-sized denominators without calculating the remainder. Since we need to calculate the remainder for most applications, and the middling performance benefits (~10% at best) and the worst case performance of ~3x slower, it's not worth using.
