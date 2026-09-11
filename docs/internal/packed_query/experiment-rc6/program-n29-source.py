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

# Restricted arithmetic source for the lead's AST-to-small-step compiler.
# Do not execute these definitions as a host-language query implementation.
# All subtraction is Lean Nat subtraction (saturating at zero) in the compiler.
# read(segment,index) returns 0 for none, or LE word value + 1 for some bits.
# read_len(segment,index) is the geometry-only bit length, including empty sentinels.
# Globals: N,W,C,BPW,SS,LS,LPS,SUPERSLOTS,SPARSESLOTS,LONGW,SPARSEW.
# W is physical cell width; BPW is the different logical BP-word width.

def rs_min(a, b):
    if a < b:
        return a
    return b


def rs_decode_default(tag):
    if tag == 0:
        return 0
    return tag - 1


def rs_chunk_rank(target, length, entry):
    excess_field = (entry // (C + 1)) % (2 * C + 2)
    ones = (excess_field + length - C) // 2
    if target == 1:
        return ones
    return length - ones


def rank_word(word, word_len, limit, target):
    effective = rs_min(limit, word_len)
    count = rs_min((effective - 1) // C + 1, 8)
    j = 0
    acc = 0
    while j < count:
        length = rs_min(C, effective - j * C)
        chunk = (word >> (j * C)) & ((1 << C) - 1)
        slot = (chunk * (C + 1) + length) * (C + 1) + length
        entry_tag = read(21, slot)
        entry = rs_decode_default(entry_tag)
        acc = acc + rs_chunk_rank(target, length, entry)
        j = j + 1
    return acc


def rs_rank(pos, bit_length, word_size, blocks_per_super, super_segment, block_segment, word_segment, target):
    q = rs_min(pos, bit_length)
    word_index = q // word_size
    super_tag = read(super_segment, word_index // blocks_per_super)
    block_tag = read(block_segment, word_index)
    word_tag = read(word_segment, word_index)
    if super_tag == 0:
        return 0
    if block_tag == 0:
        return 0
    if word_tag == 0:
        return 0
    word_len = read_len(word_segment, word_index)
    limit = q - word_index * word_size
    return super_tag - 1 + block_tag - 1 + rank_word(word_tag - 1, word_len, limit, target)


def rank_close(pos):
    return rs_rank(pos, 2 * N, BPW, BPW, 17, 18, 19, 0)


def rank_long(pos):
    return rs_rank(pos, SUPERSLOTS, LONGW, 1, 9, 10, 11, 1)


def rank_sparse(pos):
    return rs_rank(pos, SPARSESLOTS, SPARSEW, 1, 13, 14, 15, 1)


def select_word_false(word, word_len, occurrence):
    count = rs_min((word_len - 1) // C + 1, 8)
    j = 0
    while j < count:
        length = rs_min(C, word_len - j * C)
        chunk = (word >> (j * C)) & ((1 << C) - 1)
        rank_slot = (chunk * (C + 1) + length) * (C + 1) + length
        rank_tag = read(21, rank_slot)
        rank_entry = rs_decode_default(rank_tag)
        amount = rs_chunk_rank(0, length, rank_entry)
        if occurrence < amount:
            select_slot = chunk * (C + 1) + occurrence
            select_tag = read(22, select_slot)
            offset = rs_decode_default(select_tag)
            return j * C + offset + 1
        occurrence = occurrence - amount
        j = j + 1
    return 0


def select_close(index):
    if index >= N:
        return 0
    super_slot = index // SS
    sb_tag = read(1, super_slot)
    sw_tag = read(2, super_slot)
    sr_tag = read(3, super_slot)
    sf_tag = read(4, super_slot)
    if sb_tag == 0:
        return 0
    if sw_tag == 0:
        return 0
    if sr_tag == 0:
        return 0
    if sf_tag == 0:
        return 0
    sb = sb_tag - 1
    sw = sw_tag - 1
    sr = sr_tag - 1
    sf = sf_tag - 1
    if sr != 0:
        exception_rank = rank_long(super_slot)
        relative_slot = exception_rank * SS + (index - sb)
        relative_tag = read(12, relative_slot)
        if relative_tag == 0:
            return 0
        return sw * BPW + sf + relative_tag
    local_slot = super_slot * LPS + (index - sb) // LS
    lb_tag = read(5, local_slot)
    lw_tag = read(6, local_slot)
    lr_tag = read(7, local_slot)
    lf_tag = read(8, local_slot)
    if lb_tag == 0:
        return 0
    if lw_tag == 0:
        return 0
    if lr_tag == 0:
        return 0
    if lf_tag == 0:
        return 0
    lb = lb_tag - 1
    lw = lw_tag - 1
    lr = lr_tag - 1
    lf = lf_tag - 1
    base_position = (sw + lw) * BPW + lf
    base_occurrence = sb + lb
    if lr != 0:
        exception_rank = rank_sparse(local_slot)
        relative_slot = exception_rank * LS + (index - base_occurrence)
        relative_tag = read(16, relative_slot)
        if relative_tag == 0:
            return 0
        return base_position + relative_tag
    base_word = base_position // BPW
    first_tag = read(0, base_word)
    if first_tag == 0:
        return 0
    first_len = read_len(0, base_word)
    before_limit = base_position - base_word * BPW
    before_first = rank_word(first_tag - 1, first_len, before_limit, 0)
    upto_first = rank_word(first_tag - 1, first_len, first_len, 0)
    local_occurrence = index - base_occurrence
    remaining_first = upto_first - before_first
    if local_occurrence < remaining_first:
        offset_tag = select_word_false(first_tag - 1, first_len, before_first + local_occurrence)
        if offset_tag == 0:
            return 0
        return base_word * BPW + offset_tag
    second_tag = read(0, base_word + 1)
    if second_tag == 0:
        return 0
    second_len = read_len(0, base_word + 1)
    offset_tag = select_word_false(second_tag - 1, second_len, local_occurrence - remaining_first)
    if offset_tag == 0:
        return 0
    return (base_word + 1) * BPW + offset_tag

# Restricted arithmetic DSL SOURCE. Do not execute as a Python query.
# The lead compiler maps subtraction to saturating Nat subtraction and inlines
# all helper calls. See lca-interior-spec.md for constants and source equations.
# External helpers: read(segment,index) -> payload+1, 0 absent;
# word_len(segment,index) -> actual logical reply width; rank_close(pos) -> Nat.
# Published result registers: CAND_OK, CAND_SCORE, CAND_POS.
# Window registers: LCA_WIN0..3 and LCA_LEN0..3.


def cand_none():
    global CAND_OK, CAND_SCORE, CAND_POS
    CAND_OK = 0
    CAND_SCORE = 0
    CAND_POS = 0
    return 0


def cand_merge_left(left_ok, left_score, left_pos):
    global CAND_OK, CAND_SCORE, CAND_POS
    if left_ok != 0:
        if CAND_OK == 0:
            CAND_OK = left_ok
            CAND_SCORE = left_score
            CAND_POS = left_pos
        else:
            if CAND_SCORE < left_score:
                keep_right = 0
            else:
                CAND_OK = left_ok
                CAND_SCORE = left_score
                CAND_POS = left_pos
    return 0


def interior_read(entry_count, width, base, index):
    chunks = width // BPW
    if width % BPW != 0:
        chunks = chunks + 1
    if index < entry_count:
        j = 0
        value = 0
        shift = 0
        all_present = 1
        while j < chunks:
            address = base + index * chunks + j
            reply = read(20, address)
            if reply == 0:
                all_present = 0
            else:
                value = value | ((reply - 1) << shift)
                shift = shift + word_len(20, address)
            j = j + 1
        if all_present == 0:
            return 0
        else:
            return value + 1
    else:
        dead_reply = read(20, OFF_DEAD)
        return dead_reply


def interior_min_candidate(block):
    global CAND_OK, CAND_SCORE, CAND_POS
    baseline = interior_read(NS, BPW, OFF_BASELINE, block // S)
    min_rel = interior_read(NB, RW, OFF_MIN, block)
    max_rel = interior_read(NB, RW, OFF_MAX, block)
    arg = interior_read(NB, RW, OFF_ARG, block)
    dummy = cand_none()
    if baseline != 0:
        if min_rel != 0:
            if max_rel != 0:
                if arg != 0:
                    CAND_OK = 1
                    CAND_SCORE = (baseline - 1) + (min_rel - 1) - B * S
                    CAND_POS = block * B + arg - 1
    return 0


def interior_local_span(macro_index, local_start, level):
    slot = macro_index * (LC * M) + level * M + local_start
    offset = interior_read(MC * (LC * M), OW, OFF_LOCAL, slot)
    if offset == 0:
        dummy = cand_none()
    else:
        dummy = interior_min_candidate(macro_index * M + offset - 1)
    return 0


def interior_global_span(macro_start, level):
    slot = level * MC + macro_start
    block = interior_read(GC * MC, BAW, OFF_GLOBAL, slot)
    if block == 0:
        dummy = cand_none()
    else:
        dummy = interior_min_candidate(block - 1)
    return 0


def interior_local_two(macro_index, local_start, count):
    encoded_tag = interior_read(LD, LW, OFF_LOCAL_LEVEL, count)
    if encoded_tag == 0:
        dummy = cand_none()
    else:
        encoded = encoded_tag - 1
        level = encoded // LD
        span = encoded % LD
        dummy = interior_local_span(macro_index, local_start, level)
        left_ok = CAND_OK
        left_score = CAND_SCORE
        left_pos = CAND_POS
        dummy = interior_local_span(macro_index, local_start + count - span, level)
        dummy = cand_merge_left(left_ok, left_score, left_pos)
    return 0


def interior_global_two(macro_start, count):
    encoded_tag = interior_read(GD, GW, OFF_GLOBAL_LEVEL, count)
    if encoded_tag == 0:
        dummy = cand_none()
    else:
        encoded = encoded_tag - 1
        level = encoded // GD
        span = encoded % GD
        dummy = interior_global_span(macro_start, level)
        left_ok = CAND_OK
        left_score = CAND_SCORE
        left_pos = CAND_POS
        dummy = interior_global_span(macro_start + count - span, level)
        dummy = cand_merge_left(left_ok, left_score, left_pos)
    return 0


def interior_range(start_block, count):
    if count == 0:
        dummy = cand_none()
    else:
        macro_start = start_block // M
        local_start = start_block % M
        first_count = M - local_start
        if count <= first_count:
            dummy = interior_local_two(macro_start, local_start, count)
        else:
            rest = count - first_count
            middle_count = rest // M
            right_count = rest % M
            dummy = interior_local_two(macro_start, local_start, first_count)
            left_ok = CAND_OK
            left_score = CAND_SCORE
            left_pos = CAND_POS
            if middle_count == 0:
                dummy = interior_local_two(macro_start + 1, 0, right_count)
                dummy = cand_merge_left(left_ok, left_score, left_pos)
            else:
                dummy = interior_global_two(macro_start + 1, middle_count)
                dummy = cand_merge_left(left_ok, left_score, left_pos)
                if right_count != 0:
                    merged_ok = CAND_OK
                    merged_score = CAND_SCORE
                    merged_pos = CAND_POS
                    dummy = interior_local_two(macro_start + 1 + middle_count, 0, right_count)
                    dummy = cand_merge_left(merged_ok, merged_score, merged_pos)
    return 0


def load_window(close):
    global LCA_WIN0, LCA_WIN1, LCA_WIN2, LCA_WIN3
    global LCA_LEN0, LCA_LEN1, LCA_LEN2, LCA_LEN3
    first = ((close // B) * B) // BPW
    tag0 = read(0, first)
    tag1 = read(0, first + 1)
    tag2 = read(0, first + 2)
    tag3 = read(0, first + 3)
    LCA_WIN0 = tag0 - 1
    LCA_WIN1 = tag1 - 1
    LCA_WIN2 = tag2 - 1
    LCA_WIN3 = tag3 - 1
    LCA_LEN0 = 0
    LCA_LEN1 = 0
    LCA_LEN2 = 0
    LCA_LEN3 = 0
    if tag0 != 0:
        LCA_LEN0 = word_len(0, first)
    if tag1 != 0:
        LCA_LEN1 = word_len(0, first + 1)
    if tag2 != 0:
        LCA_LEN2 = word_len(0, first + 2)
    if tag3 != 0:
        LCA_LEN3 = word_len(0, first + 3)
    return 0


def window_chunk(j):
    start = j * C
    base = 0
    taken = 0
    value = 0
    k = 0
    while k < 4:
        word = LCA_WIN0
        length = LCA_LEN0
        if k == 1:
            word = LCA_WIN1
            length = LCA_LEN1
        if k == 2:
            word = LCA_WIN2
            length = LCA_LEN2
        if k == 3:
            word = LCA_WIN3
            length = LCA_LEN3
        if start < base + length:
            offset = start - base
            use = length - offset
            if C - taken < use:
                use = C - taken
            part = (word >> offset) & ((1 << use) - 1)
            value = value | (part << taken)
            taken = taken + use
        base = base + length
        k = k + 1
    return value


def fringe(close, start, span):
    global CAND_OK, CAND_SCORE, CAND_POS
    base = (((close // B) * B) // BPW) * BPW
    rank_false = rank_close(base)
    seed = base - 2 * rank_false
    dummy = load_window(close)
    rel_lo = start - base
    rel_hi = start + span - 1 - base
    count = rel_hi // C + 1
    if 33 < count:
        count = 33
    acc = seed
    best_ok = 0
    best_score = 0
    best_pos = 0
    j = 0
    while j < count:
        chunk_start = j * C
        a = rel_lo - chunk_start
        if C < a:
            a = C
        end = rel_hi + 1
        if (j + 1) * C < end:
            end = (j + 1) * C
        b = end - chunk_start
        value = window_chunk(j)
        slot = (value * (C + 1) + a) * (C + 1) + b
        entry_tag = read(21, slot)
        entry = entry_tag - 1
        if a < b:
            score = acc + (entry // (C + 1)) % (2 * C + 2) - C
            position = j * C + entry % (C + 1)
            if best_ok == 0:
                best_ok = 1
                best_score = score
                best_pos = position
            else:
                if score < best_score:
                    best_score = score
                    best_pos = position
        acc = acc + entry // ((C + 1) * (2 * C + 2)) - C
        j = j + 1
    CAND_OK = 1
    if best_ok == 0:
        CAND_SCORE = seed
        CAND_POS = start
    else:
        CAND_SCORE = best_score
        CAND_POS = base + best_pos
    return 0


def lca(left_close, right_close):
    left_block = left_close // B
    right_block = right_close // B
    if left_block == right_block:
        dummy = fringe(left_close, left_close + 1, right_close - left_close + 1)
    else:
        left_span = left_block * B + B - left_close
        dummy = fringe(left_close, left_close + 1, left_span)
        left_ok = CAND_OK
        left_score = CAND_SCORE
        left_pos = CAND_POS
        if left_block + 1 < right_block:
            dummy = interior_range(left_block + 1, right_block - left_block - 1)
        else:
            dummy = cand_none()
        dummy = cand_merge_left(left_ok, left_score, left_pos)
        merged_ok = CAND_OK
        merged_score = CAND_SCORE
        merged_pos = CAND_POS
        right_start = right_block * B
        right_span = right_close - right_start + 2
        dummy = fringe(right_close, right_start, right_span)
        dummy = cand_merge_left(merged_ok, merged_score, merged_pos)
    if CAND_OK == 0:
        return 0
    else:
        return CAND_POS - 1 + 1

def locate(segment,index):
    global LOC_OK, LOC_BIT, LOC_LEN
    LOC_OK = 0
    LOC_BIT = 0
    LOC_LEN = 0
    if segment == 0 or segment == 19:
        count = (2 * N + BPW - 1) // BPW
        if segment == 19:
            count = count + 2 * N + 1
        if index < count:
            LOC_OK = 1
            LOC_BIT = W + index * BPW
            LOC_LEN = min(BPW, 2 * N - index * BPW)
        return 0
    prefix = W + 2 * N
    bits = (12 + 0 * LONG + 0 * SPARSE)
    if segment == 17:
        if index < (2 + 0 * LONG + 0 * SPARSE):
            LOC_OK = 1
            LOC_BIT = prefix + index * 6
            LOC_LEN = min(6, bits - index * 6)
        return 0
    prefix = prefix + bits
    bits = (60 + 0 * LONG + 0 * SPARSE)
    if segment == 18:
        if index < (10 + 0 * LONG + 0 * SPARSE):
            LOC_OK = 1
            LOC_BIT = prefix + index * 6
            LOC_LEN = min(6, bits - index * 6)
        return 0
    prefix = prefix + bits
    bits = (6 + 0 * LONG + 0 * SPARSE)
    if segment == 1:
        if index < (1 + 0 * LONG + 0 * SPARSE):
            LOC_OK = 1
            LOC_BIT = prefix + index * 6
            LOC_LEN = min(6, bits - index * 6)
        return 0
    prefix = prefix + bits
    bits = (6 + 0 * LONG + 0 * SPARSE)
    if segment == 2:
        if index < (1 + 0 * LONG + 0 * SPARSE):
            LOC_OK = 1
            LOC_BIT = prefix + index * 6
            LOC_LEN = min(6, bits - index * 6)
        return 0
    prefix = prefix + bits
    bits = (6 + 0 * LONG + 0 * SPARSE)
    if segment == 3:
        if index < (1 + 0 * LONG + 0 * SPARSE):
            LOC_OK = 1
            LOC_BIT = prefix + index * 6
            LOC_LEN = min(6, bits - index * 6)
        return 0
    prefix = prefix + bits
    bits = (6 + 0 * LONG + 0 * SPARSE)
    if segment == 4:
        if index < (1 + 0 * LONG + 0 * SPARSE):
            LOC_OK = 1
            LOC_BIT = prefix + index * 6
            LOC_LEN = min(6, bits - index * 6)
        return 0
    prefix = prefix + bits
    bits = (216 + 0 * LONG + 0 * SPARSE)
    if segment == 5:
        if index < (36 + 0 * LONG + 0 * SPARSE):
            LOC_OK = 1
            LOC_BIT = prefix + index * 6
            LOC_LEN = min(6, bits - index * 6)
        return 0
    prefix = prefix + bits
    bits = (216 + 0 * LONG + 0 * SPARSE)
    if segment == 6:
        if index < (36 + 0 * LONG + 0 * SPARSE):
            LOC_OK = 1
            LOC_BIT = prefix + index * 6
            LOC_LEN = min(6, bits - index * 6)
        return 0
    prefix = prefix + bits
    bits = (216 + 0 * LONG + 0 * SPARSE)
    if segment == 7:
        if index < (36 + 0 * LONG + 0 * SPARSE):
            LOC_OK = 1
            LOC_BIT = prefix + index * 6
            LOC_LEN = min(6, bits - index * 6)
        return 0
    prefix = prefix + bits
    bits = (216 + 0 * LONG + 0 * SPARSE)
    if segment == 8:
        if index < (36 + 0 * LONG + 0 * SPARSE):
            LOC_OK = 1
            LOC_BIT = prefix + index * 6
            LOC_LEN = min(6, bits - index * 6)
        return 0
    prefix = prefix + bits
    bits = (2 + 0 * LONG + 0 * SPARSE)
    if segment == 9:
        if index < (2 + 0 * LONG + 0 * SPARSE):
            LOC_OK = 1
            LOC_BIT = prefix + index * 1
            LOC_LEN = min(1, bits - index * 1)
        return 0
    prefix = prefix + bits
    bits = (2 + 0 * LONG + 0 * SPARSE)
    if segment == 10:
        if index < (2 + 0 * LONG + 0 * SPARSE):
            LOC_OK = 1
            LOC_BIT = prefix + index * 1
            LOC_LEN = min(1, bits - index * 1)
        return 0
    prefix = prefix + bits
    bits = (1 + 0 * LONG + 0 * SPARSE)
    if segment == 11:
        if index < (3 + 0 * LONG + 0 * SPARSE):
            LOC_OK = 1
            LOC_BIT = prefix + index * 1
            LOC_LEN = min(1, bits - index * 1)
        return 0
    prefix = prefix + bits
    bits = (0 + 216 * LONG + 0 * SPARSE)
    if segment == 12:
        if index < (0 + 36 * LONG + 0 * SPARSE):
            LOC_OK = 1
            LOC_BIT = prefix + index * 6
            LOC_LEN = min(6, bits - index * 6)
        return 0
    prefix = prefix + bits
    bits = (30 + 0 * LONG + 0 * SPARSE)
    if segment == 13:
        if index < (6 + 0 * LONG + 0 * SPARSE):
            LOC_OK = 1
            LOC_BIT = prefix + index * 5
            LOC_LEN = min(5, bits - index * 5)
        return 0
    prefix = prefix + bits
    bits = (30 + 0 * LONG + 0 * SPARSE)
    if segment == 14:
        if index < (6 + 0 * LONG + 0 * SPARSE):
            LOC_OK = 1
            LOC_BIT = prefix + index * 5
            LOC_LEN = min(5, bits - index * 5)
        return 0
    prefix = prefix + bits
    bits = (29 + 0 * LONG + 0 * SPARSE)
    if segment == 15:
        if index < (36 + 0 * LONG + 0 * SPARSE):
            LOC_OK = 1
            LOC_BIT = prefix + index * 5
            LOC_LEN = min(5, bits - index * 5)
        return 0
    prefix = prefix + bits
    bits = (0 + 0 * LONG + 6 * SPARSE)
    if segment == 16:
        if index < (0 + 0 * LONG + 1 * SPARSE):
            LOC_OK = 1
            LOC_BIT = prefix + index * 6
            LOC_LEN = min(6, bits - index * 6)
        return 0
    prefix = prefix + bits
    if segment == 20:
        if index < 2:
            local = index - 0
            entry = local // 1
            chunk = local % 1
            LOC_OK = 1
            LOC_BIT = prefix + 0 + entry * 6 + chunk * BPW
            LOC_LEN = min(BPW, 6 - chunk * BPW)
            return 0
        if index < 12:
            local = index - 2
            entry = local // 2
            chunk = local % 2
            LOC_OK = 1
            LOC_BIT = prefix + 12 + entry * 9 + chunk * BPW
            LOC_LEN = min(BPW, 9 - chunk * BPW)
            return 0
        if index < 22:
            local = index - 12
            entry = local // 2
            chunk = local % 2
            LOC_OK = 1
            LOC_BIT = prefix + 57 + entry * 9 + chunk * BPW
            LOC_LEN = min(BPW, 9 - chunk * BPW)
            return 0
        if index < 32:
            local = index - 22
            entry = local // 2
            chunk = local % 2
            LOC_OK = 1
            LOC_BIT = prefix + 102 + entry * 9 + chunk * BPW
            LOC_LEN = min(BPW, 9 - chunk * BPW)
            return 0
        if index < 157:
            local = index - 32
            entry = local // 1
            chunk = local % 1
            LOC_OK = 1
            LOC_BIT = prefix + 147 + entry * 5 + chunk * BPW
            LOC_LEN = min(BPW, 5 - chunk * BPW)
            return 0
        if index < 158:
            local = index - 157
            entry = local // 1
            chunk = local % 1
            LOC_OK = 1
            LOC_BIT = prefix + 772 + entry * 3 + chunk * BPW
            LOC_LEN = min(BPW, 3 - chunk * BPW)
            return 0
        if index < 212:
            local = index - 158
            entry = local // 2
            chunk = local % 2
            LOC_OK = 1
            LOC_BIT = prefix + 775 + entry * 8 + chunk * BPW
            LOC_LEN = min(BPW, 8 - chunk * BPW)
            return 0
        if index < 215:
            local = index - 212
            entry = local // 1
            chunk = local % 1
            LOC_OK = 1
            LOC_BIT = prefix + 991 + entry * 3 + chunk * BPW
            LOC_LEN = min(BPW, 3 - chunk * BPW)
            return 0
        return 0
    prefix = prefix + 1000
    if segment == 21:
        if index < 8:
            LOC_OK = 1
            LOC_LEN = 5
            LOC_BIT = prefix + index * LOC_LEN
        return 0
    prefix = prefix + 40
    if segment == 22:
        if index < 4:
            LOC_OK = 1
            LOC_LEN = 2
            LOC_BIT = prefix + index * LOC_LEN
    return 0
