from typing import List, Optional, Union, Set
from enum import Enum
from abc import ABC, abstractmethod
from tabulate import tabulate


# Can structure a proof as a list of lists.


class Expression(ABC):
    def __init__(self):
        pass

    @abstractmethod
    def __eq__(self, other):
        raise NotImplementedError()

    @abstractmethod
    def __str__(self):
        raise NotImplementedError()


class Atom(Expression):
    def __init__(self, name: str):
        super().__init__()
        self.name = name

    def __str__(self):
        return self.name

    def __eq__(self, other):
        return isinstance(other, Atom) and self.name == other.name


class Contr(Atom):
    def __init__(self):
        super().__init__("⊥")

    def __eq__(self, other):
        return isinstance(other, Contr)


class NotExpr(Expression):
    def __init__(self, content: Expression):
        super().__init__()
        self.content = content

    def __eq__(self, other):
        return isinstance(other, NotExpr) and self.content == other.content

    def __str__(self):
        if isinstance(self.content, Atom):
            inside = self.content
        else:
            inside = f"({self.content})"
        return f"~{inside}"


class BinaryExpr(Expression, ABC):
    def __init__(self, left: Expression, right: Expression, symbol: str):
        super().__init__()
        self.left = left
        self.right = right
        self.symbol = symbol

    def __eq__(self, other):
        return isinstance(self, other.__class__) and self.left == other.left and self.right == other.right

    def __str__(self):
        if isinstance(self.left, Atom):
            left = str(self.left)
        else:
            left = f"({str(self.left)})"

        if isinstance(self.right, Atom):
            right = str(self.right)
        else:
            right = f"({str(self.right)})"

        return f"{left} {self.symbol} {right}"


class OrExpr(BinaryExpr):
    def __init__(self, left: Expression, right: Expression):
        super().__init__(left, right, "v")


class AndExpr(BinaryExpr):
    def __init__(self, left: Expression, right: Expression):
        super().__init__(left, right, "&")


class ImpExpr(BinaryExpr):
    def __init__(self, left: Expression, right: Expression):
        super().__init__(left, right, "-->")


class Reference:
    def __init__(self, line_no: int, discharge: Optional[Union[int, str]]=None):
        """

        :param line_no: The line number
        :param discharge: The assumption to discharge by index.
                          Can also be None for no discharge, or "v" for vacuous discharge.
        """
        self.line_no = line_no
        self.discharge = discharge

    def __str__(self):
        discharge = ""
        if self.discharge == "v":
            discharge = "[]"
        elif self.discharge is not None:
            discharge = f"[{self.discharge}]"
        return f"{self.line_no}{discharge}"


class References(list):
    def __init__(self, *args):
        super().__init__()
        for x in args:
            self.append(x)

    def __str__(self):
        xs = [str(x) for x in self]
        return ", ".join(xs)


class Rule(Enum):
    ASSUMPTION = 0
    AND_ELIM = 1
    AND_INTRO = 2
    DNE = 3  # Double Not Elimination
    NOT_ELIM = 4
    NOT_INTRO = 5
    OR_INTRO = 6
    OR_ELIM = 7
    IMPLIES_INTRO = 8
    IMPLIES_ELIM = 9
    RAA = 10 # Reducto Ad Absurdum

    def __str__(self):
        outs = [
            "A",
            "&E",
            "&I",
            "~~E",
            "~E",
            "~I",
            "vI",
            "vE",
            "-->I",
            "-->E",
            "RAA"
        ]
        return outs[self.value]


class ProofLine:
    def __init__(self, assumptions: Set[int], content: Expression, references: References, rule_used: Rule):
        self.assumptions = assumptions
        self.content = content
        self.references = references
        self.rule_used = rule_used

    def to_repr_list(self):
        return [self.assumptions, self.content, self.references, self.rule_used]


class Goal:
    def __init__(self, assumptions: Set[int], content: Expression):
        self.assumptions = assumptions
        self.content = content


class Proof:
    def __init__(self, premises: List[Expression], goal: Expression):
        # Everything in self.lines is assumed to be a correctly added line.
        self.lines = [ProofLine({i}, premises[i], References(), Rule.ASSUMPTION) for i in range(len(premises))]
        self.goal = Goal(set(range(len(self.lines))), goal)
        self.assumption_map = premises
        self.can_add_funcs = [
            self.can_add_assumption,
            self.can_add_and_elim,
            self.can_add_and_intro,
            self.can_add_dne,
            self.can_add_not_elim,
            self.can_add_not_intro,
            self.can_add_or_intro,
            self.can_add_or_elim,
            self.can_add_implies_intro,
            self.can_add_implies_elim,
            self.can_add_raa
        ]

    def is_complete(self):
        # Nothing has been done yet.
        if len(self.lines) == 0: return False

        # Check if the last line has matching assumptions and content.
        last_line = self.lines[-1]
        return last_line.content == self.goal.content and last_line.assumptions == self.goal.assumptions

    def try_add_line(self, line: ProofLine) -> bool:
        if self.can_add_line(line):
            if line.rule_used == Rule.ASSUMPTION:
                self.assumption_map.append(line.content)
            self.lines.append(line)
            return True
        return False

    def can_add_line(self, line: ProofLine) -> bool:
        """
        Checks if a line can be added to the proof.
        :param line: The line to check.
        :return: True, if the line can be added, and False otherwise.
        """
        return self.can_add_funcs[line.rule_used.value](line)

    def can_add_assumption(self, line: ProofLine):
        correct_assumptions = len(line.assumptions) == 1 and list(line.assumptions)[0] == len(self.assumption_map)
        if not correct_assumptions: return False

        return len(line.references) == 0

    def can_add_and_elim(self, line: ProofLine):
        correct_references = len(line.references) == 1 and line.references[0].discharge is None
        if not correct_references: return False

        reference = line.references[0].line_no
        correct_assumptions = line.assumptions == self.lines[reference].assumptions
        if not correct_assumptions: return False

        referenced = self.lines[reference].content
        if not isinstance(referenced, AndExpr): return False

        left_or_right_match = line.content == referenced.left or line.content == referenced.right
        return left_or_right_match

    def can_add_and_intro(self, line: ProofLine):
        if not isinstance(line.content, AndExpr): return False

        correct_references = (len(line.references) == 2
                              and all([reference.discharge is None for reference in line.references]))
        if not correct_references: return False

        reference1 = line.references[0]
        reference2 = line.references[1]
        correct_assumptions = (line.assumptions ==
                               self.lines[reference1.line_no].assumptions.union(
                                   self.lines[reference2.line_no].assumptions))
        if not correct_assumptions: return False

        referenced_content1 = self.lines[reference1.line_no].content
        referenced_content2 = self.lines[reference2.line_no].content
        left_and_right_match = line.content.left == referenced_content1 and line.content.right == referenced_content2
        return left_and_right_match

    def can_add_dne(self, line: ProofLine):
        correct_references = len(line.references) == 1 and line.references[0].discharge is None
        if not correct_references: return False

        reference = line.references[0].line_no
        referenced = self.lines[reference]
        correct_assumptions = line.assumptions == referenced.assumptions
        if not correct_assumptions: return False

        referenced_content = referenced.content
        if not isinstance(referenced_content, NotExpr): return False

        referenced_content_content = referenced_content.content
        if not isinstance(referenced_content_content, NotExpr): return False

        return referenced_content_content.content == line.content

    def can_add_not_elim(self, line: ProofLine):
        correct_references = (len(line.references) == 2
                              and all([line.references[i].discharge is None for i in range(2)]))
        if not correct_references: return False

        reference1 = self.lines[line.references[0].line_no]
        reference2 = self.lines[line.references[1].line_no]
        correct_assumptions = line.assumptions == reference1.assumptions.union(reference2.assumptions)
        if not correct_assumptions: return False

        referenced1 = reference1.content
        referenced2 = reference2.content
        correct_contents = (((isinstance(referenced1, NotExpr) and referenced1.content == referenced2)
                            or (isinstance(referenced2, NotExpr) and referenced1 == referenced2.content))
                            and line.content == Contr())
        return correct_contents

    def can_add_not_intro(self, line: ProofLine):
        if len(line.references) != 1: return False
        line_reference = line.references[0]
        if line_reference.discharge is None: return False

        referenced = self.lines[line_reference.line_no]
        if referenced.content != Contr(): return False

        if line_reference.discharge == "v":
            correct_assumptions = line.assumptions == referenced.assumptions
        else:
            correct_assumptions = (line.assumptions.union({line_reference.discharge}) == referenced.assumptions
                                   and len(line.assumptions) < len(referenced.assumptions))

        if not correct_assumptions: return False

        line_content = line.content
        if not isinstance(line_content, NotExpr): return False

        return ((line_reference.discharge != "v"
                and line_content.content == self.assumption_map[line_reference.discharge])
                or line_reference.discharge == "v")

    def can_add_or_intro(self, line: ProofLine):
        if not isinstance(line.content, OrExpr): return False

        correct_references = len(line.references) == 1 and line.references[0].discharge is None
        if not correct_references: return False

        reference = line.references[0]
        correct_assumptions = line.assumptions == self.lines[reference.line_no]
        if not correct_assumptions: return False

        referenced_content = self.lines[reference.line_no].content
        left_or_right_match = referenced_content == line.content.left or referenced_content == line.content.right
        return left_or_right_match

    def can_add_or_elim(self, line: ProofLine):
        if len(line.references) != 3: return False
        ref1 = line.references[0]
        ref2 = line.references[1]
        ref3 = line.references[2]

        if (ref1.discharge is not None or
                ref2.discharge in [None, "v"] or
                ref3.discharge in [None, "v"]): return False
        referenced1 = self.lines[ref1.line_no]
        referenced2 = self.lines[ref2.line_no]
        referenced3 = self.lines[ref3.line_no]

        discharge_cont2 = self.assumption_map[ref2.discharge]
        discharge_cont3 = self.assumption_map[ref3.discharge]

        referenced1_content = referenced1.content
        if not isinstance(referenced1_content, OrExpr): return False
        if (not (discharge_cont2 == referenced1_content.left and discharge_cont3 == referenced1_content.right)
            and not (discharge_cont2 == referenced1_content.right and discharge_cont2 == referenced1_content.left)):
            return False
        if not (referenced2.content == line.content and referenced3.content == line.content):
            return False

        if (line.assumptions !=
            referenced1.assumptions.union(referenced2.assumptions).union(referenced3.assumptions)
                - {ref2.discharge, ref3.discharge}):
            return False

        return True

    def can_add_implies_intro(self, line: ProofLine):
        if len(line.references) != 1: return False
        reference = line.references[0]

        if reference.discharge is None: return False

        referenced = self.lines[reference.line_no]
        line_content = line.content

        if not isinstance(line_content, ImpExpr): return False
        if reference.discharge == "v":
            if line.assumptions != referenced.assumptions: return False
            return line_content.right == referenced.content

        if line.assumptions != referenced.assumptions - {reference.discharge}: return False
        return (line_content.right == referenced.content and
                line_content.left == self.assumption_map[reference.discharge])

    def can_add_implies_elim(self, line: ProofLine):
        correct_references = (len(line.references) == 2 and
                              all([reference.discharge is None for reference in line.references]))

        if not correct_references: return False

        reference1 = line.references[0].line_no
        reference2 = line.references[1].line_no

        referenced1 = self.lines[reference1]
        referenced2 = self.lines[reference2]

        correct_assumptions = line.assumptions == referenced1.assumptions.union(referenced2.assumptions)
        if not correct_assumptions: return False

        content1 = referenced1.content
        content2 = referenced2.content
        if isinstance(content1, ImpExpr):
            imp_cont = content1
            other_cont = content2
        elif isinstance(content2, ImpExpr):
            imp_cont = content2
            other_cont = content1
        else: return False

        if imp_cont.left != other_cont: return False
        return imp_cont.right == line.content

    def can_add_raa(self, line: ProofLine):
        if len(line.references) != 2: return False
        reference1 = line.references[0]
        reference2 = line.references[1]

        if reference1.discharge is not None: return False

        referenced1 = self.lines[reference1.line_no]
        referenced2 = self.lines[reference2.line_no]
        line_content = line.content
        unioned_assumptions = referenced1.assumptions.union(referenced2.assumptions)

        if not isinstance(line_content, NotExpr): return False
        if reference2.discharge == "v":
            return line.assumptions == unioned_assumptions

        if line.assumptions != unioned_assumptions - {reference2.discharge}: return False
        return line_content.content == self.assumption_map[reference2.discharge]

    def __str__(self):
        table = [line.to_repr_list() for line in self.lines]
        return str(tabulate(table, tablefmt="plain", showindex="always"))


def parse_expr(expr: str):
    pass

if __name__ == "__main__":
    print(Rule.ASSUMPTION.value)