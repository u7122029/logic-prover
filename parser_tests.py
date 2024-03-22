import unittest
from parser import Proof, ProofLine, Atom, AndExpr, Reference, Rule, OrExpr, NotExpr, Contr, ImpExpr, References


class CanAddTests(unittest.TestCase):
    def test_and_intro_1(self):
        p = Atom("p")
        q = Atom("q")

        pf = Proof([p, q], AndExpr(p, q))
        pl = ProofLine({0, 1},
                       AndExpr(p,q),
                       [Reference(0), Reference(1)],
                       Rule.AND_INTRO)
        self.assertTrue(pf.can_add_line(pl))
        pf.lines.append(pl)
        self.assertTrue(pf.is_complete())

    def test_and_intro_2(self):
        p = Atom("p")
        q = Atom("q")
        a = AndExpr(p,q)
        b = OrExpr(q,p)

        pf = Proof([a, b], AndExpr(a, b))
        pl = ProofLine({0, 1},
                       AndExpr(a,b),
                       [Reference(0), Reference(1)],
                       Rule.AND_INTRO)
        self.assertTrue(pf.can_add_line(pl))
        pf.lines.append(pl)
        self.assertTrue(pf.is_complete())

    def test_dne_1(self):
        p = Atom("p")
        d = NotExpr(NotExpr(p))
        pf = Proof([d], p)
        pl = ProofLine({0},
                       p,
                       [Reference(0)],
                       Rule.DNE)
        self.assertTrue(pf.can_add_line(pl))
        pf.lines.append(pl)
        self.assertTrue(pf.is_complete())

    def test_not_elim_1(self):
        p = Atom("p")
        not_p = NotExpr(p)
        pf = Proof([p, not_p], Contr())
        pl = ProofLine({0, 1},
             Contr(),
             [Reference(0), Reference(1)],
             Rule.NOT_ELIM)
        self.assertTrue(pf.can_add_line(pl))
        pf.lines.append(pl)
        self.assertTrue(pf.is_complete())

    def test_not_elim_2(self):
        p = Atom("p")
        q = Atom("q")
        and_pq = AndExpr(p, q)
        not_and_pq = NotExpr(and_pq)

        pf = Proof([and_pq, not_and_pq], Contr())
        pl = ProofLine({0, 1},
                       Contr(),
                       [Reference(0), Reference(1)],
                       Rule.NOT_ELIM)
        self.assertTrue(pf.can_add_line(pl))
        pf.lines.append(pl)

        self.assertTrue(pf.is_complete())

    def test_not_intro_1(self):
        """
        Allowing p to vacuously occur from a contradiction.
        """
        c = Contr()
        p = Atom("p")
        pf = Proof([c], p)
        pl1 = ProofLine({0}, NotExpr(NotExpr(p)), [Reference(0, "v")], Rule.NOT_INTRO)
        pl2 = ProofLine({0}, p, [Reference(1)], Rule.DNE)
        self.assertTrue(pf.can_add_line(pl1))
        pf.lines.append(pl1)
        self.assertTrue(pf.can_add_line(pl2))
        pf.lines.append(pl2)

        self.assertTrue(pf.is_complete())

    def test_not_intro_2(self):
        """
        Another vacuous introduction.
        """
        c = Contr()
        p = Atom("p")
        pf = Proof([p, c], NotExpr(p))
        pls = [
            ProofLine({0, 1}, AndExpr(p,c), [Reference(0), Reference(1)], Rule.AND_INTRO),
            ProofLine({0, 1}, c, [Reference(2)], Rule.AND_ELIM),
            ProofLine({0, 1}, NotExpr(p), [Reference(3, "v")], Rule.NOT_INTRO)
        ]
        for pl in pls:
            self.assertTrue(pf.can_add_line(pl))
            pf.lines.append(pl)

        self.assertTrue(pf.is_complete())

    def test_imp_elim_1(self):
        p = Atom("p")
        q = Atom("q")
        p_imp_q = ImpExpr(p,q)
        pf = Proof([p, p_imp_q], q)
        pls = [
            ProofLine({0, 1}, q, References(Reference(0), Reference(1)), Rule.IMPLIES_ELIM)
        ]
        for pl in pls:
            self.assertTrue(pf.can_add_line(pl))
            pf.lines.append(pl)
        self.assertTrue(pf.is_complete())

    def test_imp_intro_1(self):
        c = Contr()
        p = Atom("p")
        c_imp_p = ImpExpr(c, p)
        pf = Proof([], c_imp_p)
        pls = [
            ProofLine({0}, c, References(), Rule.ASSUMPTION),
            ProofLine({0}, NotExpr(NotExpr(p)), References(Reference(0, "v")), Rule.NOT_INTRO),
            ProofLine({0}, p, References(Reference(1)), Rule.DNE),
            ProofLine(set(), c_imp_p, References(Reference(2, 0)), Rule.IMPLIES_INTRO)
        ]
        for pl in pls:
            self.assertTrue(pf.can_add_line(pl))
            if pl.rule_used == Rule.ASSUMPTION:
                pf.assumption_map.append(pl.content)
            pf.lines.append(pl)
        self.assertTrue(pf.is_complete())

    def test_imp_intro_2(self):
        p = Atom("p")
        q = Atom("q")
        p_imp_q = ImpExpr(p, q)
        pf = Proof([q], p_imp_q)
        pls = [
            ProofLine({0}, p_imp_q, References(Reference(0, "v")), Rule.IMPLIES_INTRO)
        ]
        for pl in pls:
            self.assertTrue(pf.try_add_line(pl))
        self.assertTrue(pf.is_complete())

    def test_raa_1(self):
        p = Atom("p")
        q = Atom("q")
        not_p_imp_q = ImpExpr(NotExpr(p), q)
        pf = Proof([OrExpr(p, q)], not_p_imp_q)
        pls = [
            ProofLine({1}, NotExpr(p), References(), Rule.ASSUMPTION),
            ProofLine({2}, p, References(), Rule.ASSUMPTION),
            ProofLine({1, 2}, NotExpr(NotExpr(q)),
                      References(Reference(1), Reference(2, "v")), Rule.RAA),
            ProofLine({1, 2}, q, References(Reference(3)), Rule.DNE),
            ProofLine({3}, q, References(), Rule.ASSUMPTION),
            ProofLine({0, 1}, q,
                      References(Reference(0), Reference(4, 2), Reference(5, 3)),
                      Rule.OR_ELIM),
            ProofLine({0}, not_p_imp_q, References(Reference(6, 1)), Rule.IMPLIES_INTRO)
        ]
        for pl in pls:
            self.assertTrue(pf.try_add_line(pl))
        self.assertTrue(pf.is_complete())

        print(pf)

if __name__ == '__main__':
    #x = CanAddTests()
    #x.test_not_intro_2()
    unittest.main()
