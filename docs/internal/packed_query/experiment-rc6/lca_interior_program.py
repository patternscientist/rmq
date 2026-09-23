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
