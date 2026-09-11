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
