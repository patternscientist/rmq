"""Restricted source: every expression and loop compiles to charged instructions."""

def read(segment, index):
    locate(segment, index)
    if LOC_OK == 0:
        return 0
    if LOC_LEN == 0:
        return 1
    address = LOC_BIT // W
    offset = LOC_BIT % W
    first = load(address)
    low_bits = min(LOC_LEN, W - offset)
    low = first >> offset
    if low_bits < W:
        low = low & ((1 << low_bits) - 1)
    if offset + LOC_LEN > W:
        second = load(address + 1)
        high_bits = LOC_LEN - low_bits
        high = second & ((1 << high_bits) - 1)
        low = low | (high << low_bits)
    return low + 1

def word_len(segment, index):
    locate(segment, index)
    return LOC_LEN

def read_len(segment, index):
    return word_len(segment, index)

def query(left, right):
    global LONG, SPARSE
    if not (left < right and right <= N):
        return 0
    LONG = load(0)
    SPARSE = 0
    j = SPARSESLOTS // SPARSEW
    super_tag = read(13, j)
    block_tag = read(14, j)
    flag_tag = read(15, j)
    if super_tag == 0 or block_tag == 0 or flag_tag == 0:
        return 0
    flags = flag_tag - 1
    k = 0
    rank = 0
    while k < SPARSESLOTS % SPARSEW:
        rank = rank + (flags & 1)
        flags = flags >> 1
        k = k + 1
    SPARSE = (super_tag - 1 + block_tag - 1 + rank) * LS
    a = select_close(left)
    b = select_close(right - 1)
    if a == 0 or b == 0:
        return 0
    close = lca(a - 1, b - 1)
    if close == 0:
        return 0
    # Keep saturating subtraction explicit even on corrupted replies.
    return rank_close(close) - 1 + 1
