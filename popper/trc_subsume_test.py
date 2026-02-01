from . util import  Literal, format_rule
from . trc_util import is_body_connected
from . trc_subsume import compute_core, rule_subsume_trc, atoms_subsume
from . subsume_cons import build_gen_cons, build_spe_cons
def test_all_pairing():
    # ---------- Rule r1 ----------
    r1_head = Literal(predicate="eqo", arguments=(0, 1))
    r1_body = frozenset({
        Literal(predicate="movie", arguments=(2,)),
        Literal(predicate="movie", arguments=(3,)),
        Literal(predicate="att", arguments=(2, "mid", 0)),
        Literal(predicate="att", arguments=(3, "mid", 1)),
        Literal(predicate="att", arguments=(2, "cid", 4)),
        Literal(predicate="att", arguments=(3, "cid", 4)),
        Literal(predicate="att", arguments=(3, "title", 5)),
        Literal(predicate="att", arguments=(2, "title", 6)),
        Literal(predicate="sim", arguments=(5, 6)),
    })
    r1 = (r1_head, r1_body)

    # ---------- Rule r2 ----------
    r2 = (r1_head, r1_body)
    
    # r2_head = Literal(predicate="eqo", arguments=(0, 1))
    # r2_body = frozenset({
    #     Literal(predicate="movie", arguments=(2,)),
    #     Literal(predicate="movie", arguments=(3,)),
    #     Literal(predicate="att", arguments=(2, "mid", 1)),
    #     Literal(predicate="att", arguments=(3, "mid", 0)),
    #     Literal(predicate="att", arguments=(2, "cid", 4)),
    #     Literal(predicate="att", arguments=(3, "cid", 4)),
    #     Literal(predicate="att", arguments=(3, "rid", 7)),
    #     Literal(predicate="att", arguments=(2, "title", 5)),
    #     Literal(predicate="att", arguments=(3, "title", 6)),
    #     Literal(predicate="sim", arguments=(6, 5)),
    # })
    #r2 = (r2_head, r2_body)

    # ---------- Run ALLPAIRINGS ----------
    A, C = all_pairings(r1, r2)
    print(C)
    # ---------- Pretty printing ----------
    print("\n=== Relational pairings A ===")
    for a, a_prime in A:
        print(f"  ({a.predicate}{a.arguments}, {a_prime.predicate}{a_prime.arguments})")

    print("\n=== Comparison pairings C ===")
    for c1, c2 in C:
        def fmt(c):
            t1, att1, t2, att2, typ = c
            kind = "JOIN" if typ == 0 else "SIM"
            return f"{kind}: ({t1}.{att1}, {t2}.{att2})"

        print(f"  {fmt(c1)}  <->  {fmt(c2)}")



def test_compute_core():
    """
    Test the compute_core function on a sample ER rule.
    """

    # --- Sample literals ---
    
    # attribute atoms
    att_2_mid = Literal("att", (2, "mid", 0))
    att_3_mid = Literal("att", (3, "mid", 1))
    att_2_title = Literal("att", (2, "title", 4))
    att_3_title = Literal("att", (3, "title", 4))
    att_2_rid = Literal("att", (2, "rid", 5))
    att_3_rid = Literal("att", (3, "rid", 5))  # join on rid
    att_6_title = Literal("att", (6, "title", 4))

    # similarity atom
    sim_4_4 = Literal("sim", (4, 4))  # similarity between mid variables

    # relational atoms
    rel_2 = Literal("movie", (2,))
    rel_3 = Literal("movie", (3,))
    rel_6 = Literal("movie", (6,))


    h2 = Literal('eqo', (0, 1))

    # r1 body (more specific)
    b1 = {
        Literal('movie', (2,)),
        Literal('movie', (3,)),
        Literal('att', (2, 'mid', 0)),
        Literal('att', (3, 'mid', 1)),
        Literal('att', (2, 'rid', 4)),
        Literal('att', (3, 'rid', 4)),
        Literal('cast', (5,)),
        Literal('cast', (6,)),
        Literal('att', (2, 'cid', 7)),
        Literal('att', (3, 'cid', 8)),
        Literal('att', (5, 'cid', 7)),
        Literal('att', (6, 'cid', 8)),
        Literal('att', (5, 'name', 9)),
        Literal('att', (6, 'name', 10)),
        Literal('sim', (9,10)),
        # join on rid
    }

    # head
    head = Literal("eqo", (0, 1))

    # body with attributes, relations, and similarity
    body = frozenset({
        att_2_mid,
        att_3_mid,
        att_2_title,
        att_3_title,
        att_2_rid,
        att_3_rid,
        sim_4_4,
        rel_2,
        rel_3,
        att_6_title,
        rel_6
    })

    # input rule
    rule = (head, body) # redundant sim and relational atom
    rule2 = (h2,b1) # already minimised
    # expected range pair
    range_pair = (('movie', 'mid'), ('movie', 'mid'))
    # --- Run compute_core ---
    core_rule = compute_core(rule2,range_pair)

    # --- Output results ---
    print("Original rule:")
    print(format_rule(rule2))


    print("\nComputed core:")
    print(format_rule(core_rule))
    # # --- Assertions / checks ---
    # core_body_predicates = {lit.predicate for lit in core_rule[1]}
    
    # assert "movie" in core_body_predicates, "Relational atoms with attributes should remain"
    # assert "att" in core_body_predicates, "Attribute atoms participating in comparisons should remain"
    # assert "sim" in core_body_predicates, "Similarity atom should remain if still relevant"

    print("\nTest passed: core computed and cleaned correctly.")
    
    
def test_rule_subsume_trc_positive():
    # head
    h1 = Literal('eqo', (0, 1))
    h2 = Literal('eqo', (0, 1))

    # r1 body (more specific)
    b1 = {
        Literal('movie', (2,)),
        Literal('movie', (3,)),
        Literal('att', (2, 'mid', 0)),
        Literal('att', (3, 'mid', 1)),
        Literal('att', (2, 'rid', 4)),
        Literal('att', (3, 'rid', 4)),
        Literal('cast', (5,)),
        Literal('cast', (6,)),
        Literal('att', (2, 'cid', 7)),
        Literal('att', (3, 'cid', 8)),
        Literal('att', (5, 'cid', 7)),
        Literal('att', (6, 'cid', 8)),
        Literal('att', (5, 'name', 9)),
        Literal('att', (6, 'name', 10)),
        Literal('sim', (9,10)),
        # join on rid
    }

    # r2 body (more general)
    b2 = {
        Literal('movie', (5,)),
        Literal('movie', (6,)),
        Literal('att', (5, 'mid', 0)),
        Literal('att', (6, 'mid', 1)),
        Literal('att', (5, 'rid', 4)),
        Literal('att', (6, 'rid', 4)),
    }
    
    b3 = {
        Literal('movie', (2,)),
        Literal('movie', (3,)),
        Literal('att', (2, 'mid', 0)),
        Literal('att', (3, 'mid', 1)),
        Literal('att', (2, 'rid', 4)),
        Literal('att', (3, 'rid', 5)),
        Literal('sim', (4,5)),
        # join on rid
    }
    
    
    b4 = {
        Literal('movie', (2,)),
        Literal('movie', (3,)),
        Literal('att', (2, 'mid', 7)),
        Literal('att', (3, 'mid', 8)),
        Literal('att', (2, 'rid', 4)),
        Literal('att', (3, 'rid', 4)),
        Literal('sim', (4,4)),
        Literal('cast', (5,)),
        Literal('cast', (6,)),
        Literal('att', (2, 'cid', 0)),
        Literal('att', (3, 'cid', 1)),
        Literal('att', (5, 'cid', 0)),
        Literal('att', (6, 'cid', 1)),
        Literal('att', (5, 'name', 9)),
        Literal('att', (6, 'name', 9)),
        # join on rid
    }


    b5 = {
        Literal('movie', (2,)),
        Literal('movie', (3,)),
        Literal('att', (2, 'mid', 7)),
        Literal('att', (3, 'mid', 8)),
        Literal('cast', (5,)),
        Literal('cast', (6,)),
        Literal('att', (2, 'rid', 4)),
        Literal('att', (3, 'rid', 11)),
        Literal('sim', (4,11)),
        Literal('att', (2, 'cid', 0)),
        Literal('att', (3, 'cid', 1)),
        Literal('att', (5, 'cid', 0)),
        Literal('att', (6, 'cid', 1)),
        Literal('att', (5, 'name', 9)),
        Literal('att', (6, 'name', 10)),
        Literal('sim', (9,10)),
        # join on rid
    }

    r1 = (h1, b1)
    r2 = (h2, b2)
    r3 = (h1,b3)
    r4 = (h1,b4)
    r5 = (h1,b5)

    # expected range pair
    range_pair = (('cast', 'cid'), ('cast', 'cid'))

    result = rule_subsume_trc(r5, r4, range_pair)

    assert result is True, "Expected r2 to subsume r1 under the given range pair"
    print("✅ test_rule_subsume_trc_positive passed")
    


def test_atom_subsumes_positive():
    # head
    h1 = Literal('eqo', (0, 1))
    h2 = Literal('eqo', (0, 1))

    # r1 body (more specific)
    b1 = {
        Literal('movie', (2,)),
        Literal('movie', (3,)),
        Literal('att', (2, 'mid', 0)),
        Literal('att', (3, 'mid', 1)),
        Literal('att', (2, 'rid', 4)),
        Literal('att', (3, 'rid', 4)),
        Literal('cast', (5,)),
        Literal('cast', (6,)),
        Literal('att', (2, 'cid', 7)),
        Literal('att', (3, 'cid', 8)),
        Literal('att', (5, 'cid', 7)),
        Literal('att', (6, 'cid', 8)),
        Literal('att', (5, 'name', 9)),
        Literal('att', (6, 'name', 10)),
        Literal('sim', (9,10)),
        # join on rid
    }

    # r2 body (more general)
    b2 = {
        Literal('movie', (5,)),
        Literal('movie', (6,)),
        Literal('att', (5, 'mid', 0)),
        Literal('att', (6, 'mid', 1)),
        Literal('att', (5, 'rid', 4)),
        Literal('att', (6, 'rid', 4)),
    }
    
    b3 = {
        Literal('movie', (2,)),
        Literal('movie', (3,)),
        Literal('att', (2, 'mid', 0)),
        Literal('att', (3, 'mid', 1)),
        Literal('att', (2, 'rid', 4)),
        Literal('att', (3, 'rid', 5)),
        Literal('sim', (4,5)),
        # join on rid
    }
    
    
    b4 = {
        Literal('movie', (2,)),
        Literal('movie', (3,)),
        Literal('att', (2, 'mid', 7)),
        Literal('att', (3, 'mid', 8)),
        Literal('att', (2, 'rid', 4)),
        Literal('att', (3, 'rid', 4)),
        Literal('sim', (4,4)),
        Literal('cast', (5,)),
        Literal('cast', (6,)),
        Literal('att', (2, 'cid', 0)),
        Literal('att', (3, 'cid', 1)),
        Literal('att', (5, 'cid', 0)),
        Literal('att', (6, 'cid', 1)),
        Literal('att', (5, 'name', 9)),
        Literal('att', (6, 'name', 9)),
        # join on rid
    }


    b5 = {
        Literal('movie', (2,)),
        Literal('movie', (3,)),
        Literal('att', (2, 'mid', 7)),
        Literal('att', (3, 'mid', 8)),
        Literal('cast', (5,)),
        Literal('cast', (6,)),
        Literal('att', (2, 'rid', 4)),
        Literal('att', (3, 'rid', 11)),
        Literal('sim', (4,11)),
        Literal('att', (2, 'cid', 0)),
        Literal('att', (3, 'cid', 1)),
        Literal('att', (5, 'cid', 0)),
        Literal('att', (6, 'cid', 1)),
        Literal('att', (5, 'name', 9)),
        Literal('att', (6, 'name', 10)),
        Literal('sim', (9,10)),
        # join on rid
    }

    r1 = (h1, b1)
    r2 = (h2, b2)
    r3 = (h1,b3)
    r4 = (h1,b4)
    r5 = (h1,b5)

    # expected range pair
    range_pair = (('cast', 'cid'), ('cast', 'cid'))

    result = atoms_subsume(b4, b5)

    assert result is True, "Expected r2 to subsume r1 under the given range pair"
    print("✅ test_rule_subsume_trc_positive passed")
    
    
    
def test_is_body_connected():
    # Helper to shorten literal creation
    def L(pred, *args):
        return Literal(pred, args)

    # -------------------------
    # Case 1: Single relational atom → connected
    r1 = (
        None,
        {
            L('movie', 1)
        }
    )
    assert is_body_connected(r1) is True

    # -------------------------
    # Case 2: Two relational atoms, no connection → NOT connected
    r2 = (
        None,
        {
            L('movie', 1),
            L('cast', 2)
        }
    )
    assert is_body_connected(r2) is False

    # -------------------------
    # Case 3: Attribute join connects tuple variables
    r3 = (
        None,
        {
            L('movie', 1),
            L('cast', 2),
            L('att', 1, 'mid', 10),
            L('att', 2, 'mid', 10),
        }
    )
    assert is_body_connected(r3) is True

    # -------------------------
    # Case 4: Transitive connectivity
    # 1 connected to 2, 2 connected to 3 ⇒ 1 connected to 3
    r4 = (
        None,
        {
            L('movie', 1),
            L('cast', 2),
            L('review', 3),
            L('att', 1, 'mid', 10),
            L('att', 2, 'mid', 10),
            L('att', 2, 'cid', 20),
            L('att', 3, 'cid', 20),
        }
    )
    assert is_body_connected(r4) is True

    # -------------------------
    # Case 5: Similarity atom creates connectivity
    r5 = (
        None,
        {
            L('movie', 1),
            L('cast', 2),
            L('att', 1, 'name', 10),
            L('att', 2, 'name', 11),
            L('sim', 10, 11),
        }
    )
    assert is_body_connected(r5) is True

    # -------------------------
    # Case 6: Similarity atom without attributes → NOT connected
    r6 = (
        None,
        {
            L('movie', 1),
            L('cast', 2),
            L('sim', 10, 11),
        }
    )
    assert is_body_connected(r6) is False

    # -------------------------
    # Case 7: Attribute atoms but tuple vars disconnected
    r7 = (
        None,
        {
            L('movie', 1),
            L('cast', 2),
            L('att', 1, 'mid', 10),
            L('att', 2, 'cid', 20),
        }
    )
    assert is_body_connected(r7) is False

    # -------------------------
    # Case 8: Single tuple variable with multiple attributes
    r8 = (
        None,
        {
            L('movie', 1),
            L('att', 1, 'mid', 10),
            L('att', 1, 'name', 11),
        }
    )
    assert is_body_connected(r8) is True
    
    b =  {
        Literal('movie', (2,)),
        Literal('movie', (3,)),
        Literal('att', (2, 'mid', 7)),
        Literal('att', (3, 'mid', 8)),
        Literal('cast', (5,)),
        Literal('cast', (6,)),
        Literal('att', (2, 'rid', 4)),
        Literal('att', (3, 'rid', 11)),
        Literal('sim', (4,11)),
        Literal('att', (2, 'cid', 0)),
        Literal('att', (3, 'cid', 1)),
        # Literal('att', (5, 'cid', 0)),
        Literal('att', (6, 'cid', 1)),
        Literal('att', (5, 'name', 9)),
        Literal('att', (6, 'name', 10)),
        Literal('sim', (9,10)),
        }
        # join on rid
    r9 = (
        None,
            b
    )
    assert is_body_connected(r9) is False

    print("All is_body_connected tests passed!")
    
    
    
    
def test_gen_cons():
    # head
    h1 = Literal('eqo', (0, 1))
    h2 = Literal('eqo', (0, 1))

    # r1 body (more specific)
    b1 = {
        Literal('movie', (2,)),
        Literal('movie', (3,)),
        Literal('att', (2, 'mid', 0)),
        Literal('att', (3, 'mid', 1)),
        Literal('att', (2, 'rid', 4)),
        Literal('att', (3, 'rid', 4)),
        Literal('cast', (5,)),
        Literal('cast', (6,)),
        Literal('att', (2, 'cid', 7)),
        Literal('att', (3, 'cid', 8)),
        Literal('att', (5, 'cid', 7)),
        Literal('att', (6, 'cid', 8)),
        Literal('att', (5, 'name', 9)),
        Literal('att', (6, 'name', 10)),
        Literal('sim', (9,10)),
        # join on rid
    }

    # r2 body (more general)
    b2 = {
        Literal('movie', (5,)),
        Literal('movie', (6,)),
        Literal('att', (5, 'mid', 0)),
        Literal('att', (6, 'mid', 1)),
        Literal('att', (5, 'rid', 4)),
        Literal('att', (6, 'rid', 4)),
    }
    
    b3 = {
        Literal('movie', (2,)),
        Literal('movie', (3,)),
        Literal('att', (2, 'mid', 0)),
        Literal('att', (3, 'mid', 1)),
        Literal('att', (2, 'rid', 4)),
        Literal('att', (3, 'rid', 5)),
        Literal('sim', (4,5)),
        # join on rid
    }
    
    
    b4 = {
        Literal('movie', (2,)),
        Literal('movie', (3,)),
        Literal('att', (2, 'mid', 7)),
        Literal('att', (3, 'mid', 8)),
        Literal('att', (2, 'rid', 4)),
        Literal('att', (3, 'rid', 4)),
        Literal('sim', (4,4)),
        Literal('cast', (5,)),
        Literal('cast', (6,)),
        Literal('att', (2, 'cid', 0)),
        Literal('att', (3, 'cid', 1)),
        Literal('att', (5, 'cid', 0)),
        Literal('att', (6, 'cid', 1)),
        Literal('att', (5, 'name', 9)),
        Literal('att', (6, 'name', 9)),
        # join on rid
    }


    b5 = {
        Literal('movie', (2,)),
        Literal('movie', (3,)),
        Literal('att', (2, 'mid', 7)),
        Literal('att', (3, 'mid', 8)),
        Literal('cast', (5,)),
        Literal('cast', (6,)),
        Literal('att', (2, 'rid', 4)),
        Literal('att', (3, 'rid', 11)),
        Literal('sim', (4,11)),
        Literal('att', (2, 'cid', 0)),
        Literal('att', (3, 'cid', 1)),
        Literal('att', (5, 'cid', 0)),
        Literal('att', (6, 'cid', 1)),
        Literal('att', (5, 'name', 9)),
        Literal('att', (6, 'name', 10)),
        Literal('sim', (9,10)),
        # join on rid
    }

    r1 = (h1, b1)
    r2 = (h2, b2)
    r3 = (h1,b3)
    r4 = (h1,b4)
    r5 = (h1,b5)

    # expected range pair
    range_pair = (('movie', 'mid'), ('movie', 'mid'))

    result = build_gen_cons(r1, range_pair)
    spec = build_spe_cons(r1,range_pair)
    [print(c) for c in result]
    print(spec)