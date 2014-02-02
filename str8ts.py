#!/usr/bin/env python
from itertools import combinations, tee, product
from collections import Counter, defaultdict as DefaultDict
from argparse import ArgumentParser, RawDescriptionHelpFormatter
from copy import deepcopy
from fnmatch import fnmatch
from textwrap import dedent

BLACK = '#'
UNKNOWN = ['.', ' ', '*']
ALL = ['1', '2', '3', '4', '5', '6', '7', '8', '9']
BLACK_ALL = 'abcdefghi'

ACROSS = '123456789'
DOWN = 'ABCDEFGHI'

def _pass(s):
    print('\033[40;92mPASS\033[0m {}'.format(s))

def _fail(s):
    print('\033[40;91mFAIL\033[0m {}'.format(s))

def _todo(s):
    print('\033[103;30mTODO\033[0m {}'.format(s))

def _hit(s):
    print('\033[100;92mHIT\033[0m {}'.format(s))

def _caution(s):
    print('\033[107;92mCAUTION\033[0m {}'.format(s))

def _miss(s):
    print('\033[100;31mMISS\033[0m {}'.format(s))

def _critical(s):
    print('\033[101;97mCRITICAL\033[0m {}'.format(s))

def _comment(s):
    print('\033[100;97m#    {:<88}\033[0m'.format(s))

######################################################################################################################
    # Cell and ProxyCell classes

class Cell(object):

    def __init__(self, digits):
        self.black = False
        self.given = False
        self.digits = [ ]
        self.removed = set()
        self.sure_candidates_by_row = set()
        self.sure_candidates_by_col = set()

        for d in digits:
            if d == BLACK:
                self.black = True
            elif d in BLACK_ALL:
                self.black = True
                self.digits.append(str(ord(d) - 96))
            elif d in ALL:
                self.digits.append(d)
                self.given = True
            elif d in UNKNOWN:
                self.digits.extend(ALL)

        if len(self.digits) == 1:
            self.known = True
        else:
            self.known = False

    def __str__(self):
        if self.is_known():
            digit = self.digits[0]
        else:
            digit = ' '

        if self.black:
            return '\033[40;97m{}\033[0m'.format(digit)
        elif self.given:
            return '\033[107;94m{}\033[0m'.format(digit)
        elif self.is_known():
            return '\033[107;30m{}\033[0m'.format(digit)
        else:
            return '\033[100;30m \033[0m'

    def __repr__(self):
        if self.black:
            parts = ['\033[40;97m']
        elif self.is_unknown():
            parts = ['\033[100;30m']
        elif self.is_known():
            parts = ['\033[107;30m']
        elif self.given:
            parts = ['\033[107;94m']
        else:
            parts = ['\033[100;30m']

        for x in ALL:
            if x in self.removed:
                parts.append('\033[31m{}\033[30m'.format(x))
            elif x in self.digits:
                if self.is_known():
                    parts.append(x)
                else:
                    sc_row = x in self.sure_candidates_by_row
                    sc_col = x in self.sure_candidates_by_col
                    if sc_row and sc_col:
                        parts.append('\033[42m{}\033[100m'.format(x))
                    elif sc_row:
                        parts.append('\033[43m{}\033[100m'.format(x))
                    elif sc_col:
                        parts.append('\033[46m{}\033[100m'.format(x))
                    else:
                        parts.append(x)
            else:
                parts.append(' ')
        parts.append('\033[0m')

        self.removed.clear()
        return ''.join(parts)

    def match(self, other):
        if self.is_black():
            if other in BLACK_ALL:
                return self.digits[0] == str(ord(other) - 96)
            else:
                return other == BLACK
        else:
            return set(self.digits) == set([d for d in other])

    def is_black(self):
        return self.black

    def is_white(self):
        return not self.black

    def is_known(self):
        return self.known

    def is_unknown(self):
        return not self.known and not self.black

    def value(self):
        assert self.is_known()
        return self.digits[0]

    def can_not_be(self, n):
        if self.is_unknown():
            for d in n:
                if d in self.digits:
                    self.digits.remove(d)
                    self.removed.add(d)
                    if d in self.sure_candidates_by_row:
                        self.sure_candidates_by_row.remove(d)
                    if d in self.sure_candidates_by_col:
                        self.sure_candidates_by_col.remove(d)
            if len(self.digits) == 1:
                self.known = True

    def value_is(self, n):
        assert(n in self.digits)
        for d in self.digits:
            if d != n:
                self.removed.add(d)
        self.digits = [n]
        self.known = True

    def get_sc_by_row(self):
        return self.sure_candidates_by_row

    def get_sc_by_col(self):
        return self.sure_candidates_by_col


class ProxyCell(object):
    def __init__(self, digits, cell):
        self.digits = set(digits)
        self.cell = cell

    def can_not_be(self, n):
        self.cell.can_not_be(n)

######################################################################################################################
    # Solver functions

def generate_compartments_by_cell(cells):
    compartments = [ ]
    compartment = [ ]
    for c in cells:
        if c.is_white():
            compartment.append(c)
        elif compartment:
            compartments.append(compartment)
            compartment = [ ]
    else:
        if compartment:
            compartments.append(compartment)
    return compartments

def compartment_range_check_by_cells(compartment):
    reach = len(compartment) - 1

    # Digit:  1 2 3 4 5 6 7 8 9
    # Count:  2 2 2 2 4 4 4 5 5
    # Min:    2 - - - 2 1 - - -
    #  +->    1-1 - - 1-2 - - -
    #  +->    1-1 - - 1-1-1 - -
    #         x x|- - - - - - -

    # For each cell we test is any other cell contains digits that are out of range.
    lowest = set()
    highest = set()
    for c in compartment:
        min_digit_index = ALL.index(min(c.digits))
        while min_digit_index < 9 and min_digit_index in lowest:
            min_digit_index += 1
        else:
            lowest.add(min_digit_index)

        max_digit_index = ALL.index(max(c.digits))
        while max_digit_index >= 0 and max_digit_index in highest:
            max_digit_index -= 1
        else:
            highest.add(max_digit_index)

    digits_out_of_range = ALL[:max(max(lowest) - reach, 0)] + \
                          ALL[min(highest) + reach + 1:]

    if digits_out_of_range:
        for c in compartment:
            c.can_not_be(digits_out_of_range)

def sure_candidates_by_cells(compartment, line, sc_fn):
    union = set()
    for c in compartment:
        union.update(sc_fn(c))
    if union:
        # We can remove the sure candidates from all other cells outside of the compartment
        for c in line:
            if c in compartment:
                continue
            else:
                c.can_not_be(union)

def singles_by_cell(compartment, sc_fn):
    # Search for singles in the sure candidates
    digit_in_cells = DefaultDict(set)
    for c in compartment:
        for d in sc_fn(c):
            digit_in_cells[d].add(c)

    # If any sure candidate is only in one cell, then cell is the sure candidate
    for d, cells in digit_in_cells.iteritems():
        if len(cells) == 1:
            c = cells.pop()
            c.value_is(d)

def stranded_digits_by_cells(compartment):
    def yield_groups(union_of_compartment):
        g = [ ]
        for n in ALL:
            if n in union_of_compartment:
                g.append(n)
            elif g:
                yield g
                g = [ ]
        else:
            if g:
                yield(g)

    # We now union the available digits in the group.
    union = set()
    for c in compartment:
        union.update(c.digits)

    len_compartment = len(compartment)
    for g in yield_groups(union):
        if len(g) < len_compartment:
            # The compartment doesn't fit into this group.
            # Remove all digits of the group from the compartment digits.
            for d in g:
                for c in compartment:
                    c.can_not_be(d)

def bridging_digits_by_cells(compartment):
    siblings = { '1': '2',  '2': '13', '3': '24', '4': '35', '5': '46',
                 '6': '57', '7': '68', '8': '79', '9': '8' }
    if len(compartment) > 1:
        for cell in compartment:
            remove = set()
            for d in cell.digits:
                searching_for = siblings[d]
                # We check in another cell can touch this digit.
                hit = False
                for c in compartment:
                    if c != cell:
                        for s in searching_for:
                            if s in c.digits:
                                hit = True
                                break
                    if hit:
                        break
                else:
                    remove.add(d)
            for d in remove:
                cell.can_not_be(d)

def stranded_by_bridge_by_cells(compartment):
    counts = Counter()
    for c in compartment:
        for d in c.digits:
            counts[d] += 1
    # Search for a cell that has multiple singles
    for c in compartment:
        singles = set(d for d in c.digits if counts[d] == 1)
        if len(singles) > 1:
            # If a single can only be in a solution *including* another solution, then it is removed.
            len_compartment = len(compartment)
            min_digit, max_digit = min(counts), max(counts)
            min_digit_index, max_digit_index = ALL.index(min_digit), ALL.index(max_digit)
            solutions = [ALL[i:i + len_compartment] for i in range(min_digit_index, max_digit_index + 2 - len_compartment)]

            isolated_singles = set()
            for s in solutions:
                found_singles = set(single for single in singles if single in s)
                if len(found_singles) == 1:
                    isolated_singles.update(found_singles)
            for s in singles:
                if s not in isolated_singles:
                    # This single is illegal.
                    for c in compartment:
                        c.can_not_be(s)

def naked_groups_by_cells(cells):
    # For each line we consider all combinations searching for naked groups
    for r in xrange(len(cells), 1, -1):
        for combination in combinations(cells, r):
            digits = set()
            for c in combination:
                digits.update(c.digits)
            if len(digits) == r:
                # We need to check that there isn't another cell which can be added to this group,
                # if so, it would have all it's digits removed.
                for c in cells:
                    if c in combination:
                        continue
                    elif not digits.issuperset(c.digits):
                        # We have a naked group. Exclude this digits from the other cells.
                        c.can_not_be(digits)

def split_compartments_by_cells(compartment):
    steps = [
        naked_groups_by_cells,              # yes
        # ??? We want to add this to the test, but it takes a whole board not the split cells
        # unique_rectangle_rule,
    ]
    union = set()
    for c in compartment:
        union.update(c.digits)
    for g in ALL:
        if g not in union:
            below = set(d for d in union if d < g)
            above = set(d for d in union if d > g)
            if below and above:
                #print('Split compartment col:{}{} below:{} gap:{} above:{}'.format(x, compartment, below, g, above))
                above_cells = [ProxyCell(below.intersection(c.digits), c) for c in compartment]
                below_cells = [ProxyCell(above.intersection(c.digits), c) for c in compartment]
                for s in steps:
                    s(above_cells)
                    s(below_cells)

def mind_the_gap_by_cells(cells):
    def _pairwise(iter):
        a, b = tee(iter)
        next(b, None)
        return zip(a, b)

    # We search for cells with a large gap
    # Gap is 'large' if the distance is >= the compartment size
    len_compartment = len(cells)
    for cell in cells:
        for d1, d2 in _pairwise(cell.digits):
            index_d1, index_d2 = ALL.index(d1), ALL.index(d2)
            if index_d2 - index_d1 >= len_compartment:
                if not set(ALL[:index_d1]).intersection(cell.digits):
                    # These numbers can't be in the other cells
                    for c in cells:
                        if c != cell:
                            c.can_not_be(d1)
                if not set(ALL[index_d2 + 1:]).intersection(cell.digits):
                    # These numbers can't be in the other cells
                    for c in cells:
                        if c != cell:
                            c.can_not_be(d2)

def mind_the_bridging_gap_by_cells(cells):
    len_compartment = len(cells)
    small_cells = [c for c in cells if len(c.digits) == 2]
    # We search for 2 cells with only 2 digits, a shared digit and a large gap
    for combination in combinations(small_cells, 2):
        a_digits = set(combination[0].digits)
        b_digits = set(combination[1].digits)
        bridge = a_digits.intersection(b_digits)
        if len(bridge) == 1:
            a_index = ALL.index(a_digits.difference(bridge).pop())
            b_index = ALL.index(b_digits.difference(bridge).pop())
            if (a_index > b_index and a_index - b_index >= len_compartment) or \
               (b_index - a_index >= len_compartment):
               # We can remove the bridge from all other cells
                for c in cells:
                    if c not in combination:
                        c.can_not_be(bridge)

def hidden_group_by_cells(compartment, sc_fn):
    union = set()
    for c in compartment:
        union.update(sc_fn(c))
    if union:
        for r in xrange(2, len(union)):
            for combination in combinations(union, r):
                # We count the cells that have contain these sure candidates
                cells = set()
                for c in compartment:
                    for d in combination:
                        if d in c.digits:
                            cells.add(c)
                            break
                # If the # of cells containing the combination is equal
                if len(cells) == r:
                    can_not_be = set(ALL)
                    can_not_be.difference_update(combination)
                    # Then we remove all the other candidates from the cells.
                    for c in cells:
                        c.can_not_be(can_not_be)

def hidden_group_by_cross_cells(compartment, sure_candidates):
    for r in xrange(2, len(sure_candidates)):
        for combination in combinations(sure_candidates, r):
            # We count the cells that have contain these sure candidates
            cells = set()
            for c in compartment:
                for d in combination:
                    if d in c.digits:
                        cells.add(c)
                        break
            # If the # of cells containing the combination is equal
            if len(cells) == r:
                can_not_be = set(ALL)
                can_not_be.difference_update(combination)
                # Then we remove all the other candidates from the cells.
                for c in cells:
                    c.can_not_be(can_not_be)

def sure_candidate_upgrade_by_cells(compartments, sure_candidates, sc_fn):
    hit = False
    for d in sure_candidates:
        # If d is only in 1 compartment then it is a sure candidate.
        compartment_count = 0
        for compartment in compartments:
            for cell in compartment:
                if d in cell.digits:
                    compartment_count += 1
                    break
        if compartment_count == 1:
            for compartment in compartments:
                for cell in compartment:
                    if d in cell.digits and d not in sc_fn(cell):
                        sc_fn(cell).add(d)
                        hit = True
    return hit

def sure_candidate_range_check_by_cells(compartment, sc_fn):
    # We need to make sure that all digits are within range of the sure candidates.
    sc_for_compartment = [sc_fn(c) for c in compartment if sc_fn(c)]
    if sc_for_compartment:
        sc_min = min(min(sc) for sc in sc_for_compartment)
        sc_max = max(max(sc) for sc in sc_for_compartment)
        sc_min_index = ALL.index(sc_min)
        sc_max_index = ALL.index(sc_max)

        len_compartment = len(compartment)
        out_of_range = ALL[:max(sc_max_index - len_compartment + 1, 0)] + ALL[sc_min_index + len_compartment:]
        if out_of_range:
            if False:
                print('compartment', compartment)
                print('sc for compartment', sc_for_compartment)
                print('out of range', out_of_range)
            for c in compartment:
                c.can_not_be(out_of_range)

######################################################################################################################
    # Board class

class Board(dict):

    def __init__(self, board, chain_length=4):
        if isinstance(board, list):
            for ny, y in enumerate(DOWN):
                for nx, x in enumerate(ACROSS):
                    try:
                        digits = board[ny][nx]
                    except:
                        digits = BLACK
                    self[x, y] = Cell(digits)
        else:
            for y, line in enumerate(board.splitlines()):
                for x, c in enumerate(line):
                    self[ACROSS[x], DOWN[y]] = Cell(c)

        self.chain_length = chain_length
        # Generate and store compartments
        self.compartments_by_row = self._generate_compartments_by_row()
        self.compartments_by_col = self._generate_compartments_by_col()
        # Generate and store the sure candidates
        self.sure_candidates_by_cross_row = DefaultDict(set)
        self.sure_candidates_by_cross_col = DefaultDict(set)
        self._sure_candidates_by_row()
        self._sure_candidates_by_col()
        # Known digits
        self._known_cells = { }
        self.counts = Counter()
        self.hits = Counter()

######################################################################################################################
    # Methods to generate and iterate the compartments

    def _generate_compartments_by_row(self):
        return { y: generate_compartments_by_cell([self[x, y] for x in ACROSS]) for y in DOWN }

    def _generate_compartments_by_col(self):
        return { x: generate_compartments_by_cell([self[x, y] for y in DOWN]) for x in ACROSS }

    def _iter_compartments_by_row(self):
        for y in DOWN:
            for c in self.compartments_by_row[y]:
                yield y, c

    def _iter_compartments_by_col(self):
        for x in ACROSS:
            for c in self.compartments_by_col[x]:
                yield x, c

    def _iter_cross_but(self, x, y):
        for dx in ACROSS:
            if dx == x:
                continue
            yield (dx, y), self[dx, y]
        for dy in DOWN:
            if dy == y:
                continue
            yield (x, dy), self[x, dy]

    def _iter_all_but(self, x, y):
        for dx in ACROSS:
            if dx == x:
                continue
            for dy in DOWN:
                if dy == y:
                    continue
                yield (dx, dy), self[dx, dy]

######################################################################################################################
    # Methods to generate the sure candidates

    def _sure_candidates_by_row(self, remove_unusable=False):
        for y in DOWN:
            if len(self.compartments_by_row[y]) > 1:
                compartment_combinations = [ ]
                total_length = 0
                for compartment in self.compartments_by_row[y]:
                    # Generate a sorted list of all the digits used in the compartment.
                    union = set()
                    for c in compartment:
                        union.update(c.digits)
                    union_list = sorted(union)

                    # Generate all possible combinations of str8ts for the compartment.
                    len_compartment = len(compartment)
                    c_combinations = [ ]
                    for n in xrange(1 + len(union_list) - len_compartment):
                        index_start = ALL.index(union_list[n])
                        index_end = ALL.index(union_list[n + len_compartment - 1])
                        if index_end - index_start == len_compartment - 1:
                            c_combinations.append(set(union_list[n:n + len_compartment]))

                    # These are stored for each compartment.
                    compartment_combinations.append(c_combinations)
                    total_length += len_compartment

                # If we have more than 1 compartment we make all the possible combinations that are legal.
                row_unions = [ ]
                legal_compartments = [[ ] for c in compartment_combinations]
                for combinations in product(*compartment_combinations):
                    union = set.union(*combinations)
                    # Is a legal combination
                    if len(union) == total_length:
                        # Make a union for the row
                        row_unions.append(union)
                        # Add the legal combinations to their compartment lists.
                        for n, c in enumerate(combinations):
                            legal_compartments[n].append(c)

                row_union = set.intersection(*row_unions)
                self.sure_candidates_by_cross_row[y].update(row_union)
                for n, legal_unions in enumerate(legal_compartments):
                    compartment_union = set.union(*legal_unions)
                    compartment_intersection = set.intersection(*legal_unions)
                    for c in self.compartments_by_row[y][n]:
                        if remove_unusable:
                            for d in c.digits:
                                if d not in compartment_union:
                                    c.can_not_be(d)
                        c.sure_candidates_by_row.update(compartment_intersection)
                        c.sure_candidates_by_row.intersection_update(c.digits)
            else:
                for compartment in self.compartments_by_row[y]:
                    union = set()
                    for c in compartment:
                        union.update(c.digits)

                    index_min = ALL.index(min(union))
                    index_max = ALL.index(max(union)) + 1 # Required for correct range
                    len_compartment = len(compartment)
                    lowest_range = set(ALL[index_min:index_min + len_compartment])
                    highest_range = set(ALL[index_max - len_compartment:index_max])
                    intersection = lowest_range.intersection(highest_range)

                    if intersection:
                        # Add the sure candidates to each cell assuming they're present.
                        self.sure_candidates_by_cross_row[y].update(intersection)
                        for c in compartment:
                            # Add the intersection to each cell.
                            c.sure_candidates_by_row.update(intersection)
                            # Remove any that aren't possible.
                            c.sure_candidates_by_row.intersection_update(c.digits)

    def _sure_candidates_by_col(self, remove_unusable=False):
        for x in ACROSS:
            if len(self.compartments_by_col[x]) > 1:
                compartment_combinations = [ ]
                total_length = 0
                for compartment in self.compartments_by_col[x]:
                    # Generate a sorted list of all the digits used in the compartment.
                    union = set()
                    for c in compartment:
                        union.update(c.digits)
                    union_list = sorted(union)

                    # Generate all possible combinations of str8ts for the compartment.
                    len_compartment = len(compartment)
                    c_combinations = [ ]
                    for n in xrange(1 + len(union_list) - len_compartment):
                        index_start = ALL.index(union_list[n])
                        index_end = ALL.index(union_list[n + len_compartment - 1])
                        if index_end - index_start == len_compartment - 1:
                            c_combinations.append(set(union_list[n:n + len_compartment]))

                    # These are stored for each compartment.
                    compartment_combinations.append(c_combinations)
                    total_length += len_compartment

                # If we have more than 1 compartment we make all the possible combinations that are legal.
                col_unions = [ ]
                legal_compartments = [[ ] for c in compartment_combinations]
                for combinations in product(*compartment_combinations):
                    union = set.union(*combinations)
                    # Is a legal combination
                    if len(union) == total_length:
                        # Make a union for the row
                        col_unions.append(union)
                        # Add the legal combinations to their compartment lists.
                        for n, c in enumerate(combinations):
                            legal_compartments[n].append(c)

                col_union = set.intersection(*col_unions)
                self.sure_candidates_by_cross_col[x].update(col_union)
                for n, legal_unions in enumerate(legal_compartments):
                    compartment_union = set.union(*legal_unions)
                    compartment_intersection = set.intersection(*legal_unions)
                    for c in self.compartments_by_col[x][n]:
                        if remove_unusable:
                            for d in c.digits:
                                if d not in compartment_union:
                                    c.can_not_be(d)
                        c.sure_candidates_by_col.update(compartment_intersection)
                        c.sure_candidates_by_col.intersection_update(c.digits)
            else:
                for compartment in self.compartments_by_col[x]:
                    union = set()
                    for c in compartment:
                        union.update(c.digits)

                    index_min = ALL.index(min(union))
                    index_max = ALL.index(max(union)) + 1 # Required for correct range
                    len_compartment = len(compartment)
                    lowest_range = set(ALL[index_min:index_min + len_compartment])
                    highest_range = set(ALL[index_max - len_compartment:index_max])
                    intersection = lowest_range.intersection(highest_range)

                    if intersection:
                        # Add the sure candidates to each cell assuming they're present.
                        self.sure_candidates_by_cross_col[x].update(intersection)
                        for c in compartment:
                            # Add the intersection to each cell.
                            c.sure_candidates_by_col.update(intersection)
                            # Remove any that aren't possible.
                            c.sure_candidates_by_col.intersection_update(c.digits)

######################################################################################################################

    def __str__(self):
        lines = [ '  123456789']
        for y in DOWN:
            line = ''.join([str(self[x, y]) for x in ACROSS])
            lines.append('%s %s' % (y, line))
        return '\n'.join(lines)

    def __repr__(self):
        return self._to_string()

    def _to_string(self, lean=False, sure_candidates=False):
        def _sc(y, sc_attribute):
            line = [ ]
            for x in ACROSS:
                sc = getattr(self[x, y], sc_attribute)
                parts = [ ]
                for d in ALL:
                    if d in sc:
                        parts.append(d)
                    else:
                        parts.append(' ')
                line.append(''.join(parts))
            return '|'.join(line)

        key = '\033[43;30mR\033[100m+\033[46;30mC\033[100m=\033[42;30mB\033[0m'
        header  = key + '  1         2         3         4         5         6         7         8         9'
        divider = '  +---------+---------+---------+---------+---------+---------+---------+---------+---------+'
        lines = [header, divider]
        for y in DOWN:
            # Help with debugging the tests
            if lean:
                for x in ACROSS:
                    if self[x, y].is_white():
                        break
                else:
                    break

            parts = [repr(self[x, y]) for x in ACROSS]
            line = '|'.join(parts)
            lines.append('%s |%s|' % (y, line))
            if sure_candidates:
                lines.append(' R|%s|' % _sc(y, 'sure_candidates_by_row'))
                lines.append(' C|%s|' % _sc(y, 'sure_candidates_by_col'))
            lines.append(divider)
        return '\n'.join(lines)

    def _clear_removed(self):
        for v in self.values():
            v.removed.clear()

    def _dump_compartments(self):
        lines = [ ]
        for x, y in zip(ACROSS, DOWN):
            by_row = ' '.join(self.compartments_by_row[y])
            by_col = ' '.join(self.compartments_by_col[x])
            lines.append('{}: {:<10} {}: {}'.format(y, by_row, x, by_col))
        return '\n'.join(lines)

    def _completeness(self):
        completeness = 0
        for c in self.itervalues():
            if c.is_known():
                completeness += 9
            else:
                completeness += 9 - len(c.digits)
        return completeness 

    class InvalidSolution(Exception):
        pass

    def _valid(self):
        for _, c in self.iteritems():
            if c.is_white():
                if len(c.digits) == 0:
                    raise Board.InvalidSolution(x, y, c.digits)

        for y in DOWN:
            seen = set()
            for x in ACROSS:
                c = self[x, y]
                if c.is_known():
                    d = c.value()
                    if d in seen:
                        raise Board.InvalidSolution(x, y, d)
                    else:
                        seen.add(d)

        for x in ACROSS:
            seen = set()
            for y in DOWN:
                c = self[x, y]
                if c.is_known():
                    d = c.value()
                    if d in seen:
                        raise Board.InvalidSolution(x, y, d)
                    else:
                        seen.add(d)

    def __eq__(self, other):
        for ny, y in enumerate(DOWN):
            for nx, x in enumerate(ACROSS):
                try:
                    digits = other[ny][nx]
                except:
                    digits = BLACK
                if self[x, y].match(digits):
                    pass
                else:
                    _fail('{}{} is {} expected {}'.format(x, y, ''.join(self[x, y].digits), digits))
                    return False
        return True

######################################################################################################################

    def remove_used_digits(self):
        for (cx, cy), c in self.iteritems():
            if c.is_known() and (cx, cy) not in self._known_cells:
                cn = c.value()
                for x in ACROSS:
                    self[x, cy].can_not_be(cn)
                for y in DOWN:
                    self[cx, y].can_not_be(cn)
                self._known_cells[cx, cy] = c

    def compartment_range_check_by_row(self):
        for _, compartment in self._iter_compartments_by_row():
            compartment_range_check_by_cells(compartment)

    def compartment_range_check_by_col(self):
        for _, compartment in self._iter_compartments_by_col():
            compartment_range_check_by_cells(compartment)

    def sure_candidates_by_row(self):
        self._sure_candidates_by_row(True)
        for y, compartment in self._iter_compartments_by_row():
            sure_candidates_by_cells(compartment, [self[x, y] for x in ACROSS], Cell.get_sc_by_row)

    def sure_candidates_by_col(self):
        self._sure_candidates_by_col(True)
        for x, compartment in self._iter_compartments_by_col():
            sure_candidates_by_cells(compartment, [self[x, y] for y in DOWN], Cell.get_sc_by_col)

    def singles_by_row(self):
        for _, compartment in self._iter_compartments_by_row():
            singles_by_cell(compartment, Cell.get_sc_by_row)

    def singles_by_col(self):
        for _, compartment in self._iter_compartments_by_col():
            singles_by_cell(compartment, Cell.get_sc_by_col)

    def stranded_digits_by_row(self):
        for _, compartment in self._iter_compartments_by_row():
            stranded_digits_by_cells(compartment)

    def stranded_digits_by_col(self):
        for _, compartment in self._iter_compartments_by_col():
            stranded_digits_by_cells(compartment)

    def bridging_digits_by_row(self):
        for _, compartment in self._iter_compartments_by_row():
            bridging_digits_by_cells(compartment)

    def bridging_digits_by_col(self):
        for _, compartment in self._iter_compartments_by_col():
            bridging_digits_by_cells(compartment)

    def stranded_by_bridge_by_row(self):
        for _, compartment in self._iter_compartments_by_row():
            stranded_by_bridge_by_cells(compartment)

    def stranded_by_bridge_by_col(self):
        for _, compartment in self._iter_compartments_by_col():
            stranded_by_bridge_by_cells(compartment)

    def split_compartments_by_row(self):
        for _, compartment in self._iter_compartments_by_row():
            split_compartments_by_cells(compartment)

    def split_compartments_by_col(self):
        for _, compartment in self._iter_compartments_by_col():
            split_compartments_by_cells(compartment)

    def mind_the_gap_by_row(self):
        for _, compartment in self._iter_compartments_by_row():
            mind_the_gap_by_cells(compartment)

    def mind_the_gap_by_col(self):
        for _, compartment in self._iter_compartments_by_col():
            mind_the_gap_by_cells(compartment)

    def mind_the_bridging_gap_by_row(self):
        for _, compartment in self._iter_compartments_by_row():
            mind_the_bridging_gap_by_cells(compartment)

    def mind_the_bridging_gap_by_col(self):
        for _, compartment in self._iter_compartments_by_col():
            mind_the_bridging_gap_by_cells(compartment)

    def naked_groups_by_row(self):
        for y in DOWN:
            naked_groups_by_cells([self[x, y] for x in ACROSS if self[x, y].is_unknown()])

    def naked_groups_by_col(self):
        for x in ACROSS:
            naked_groups_by_cells([self[x, y] for y in DOWN if self[x, y].is_unknown()])

    def hidden_group_by_row(self):
        for _, compartment in self._iter_compartments_by_row():
            hidden_group_by_cells(compartment, Cell.get_sc_by_row)

    def hidden_group_by_col(self):
        for _, compartment in self._iter_compartments_by_col():
            hidden_group_by_cells(compartment, Cell.get_sc_by_col)

    def hidden_group_by_cross_row(self):
        for y in DOWN:
            hidden_group_by_cross_cells([self[x, y] for x in ACROSS], self.sure_candidates_by_cross_row[y])

    def hidden_group_by_cross_col(self):
        for x in ACROSS:
            hidden_group_by_cross_cells([self[x, y] for y in DOWN], self.sure_candidates_by_cross_col[x])

    def sea_creatures_by_row(self):
        def _sea_creatures_by_row(d):
            hit = False
            d_sure_candidates = { }
            for y in DOWN:
                candidates = set([x for x in ACROSS if self[x, y].is_unknown() and d in self[x, y].sure_candidates_by_row])
                if candidates:
                    d_sure_candidates[y] = candidates

            # ??? Is it better to search from large to small?
            for r in xrange(2, len(d_sure_candidates) + 1):
                for combination in combinations(d_sure_candidates, r):
                    # Merge the combinations
                    d_sure_union = set()
                    for c in combination:
                        d_sure_union.update(d_sure_candidates[c])

                    if len(d_sure_union) == r:
                        # We have a sea creature
                        # We can remove 'd' from all the other rows not included this combination that ..
                        # ... have 'd's in the union col.
                        for x in d_sure_union:
                            self.sure_candidates_by_cross_col[x].add(d)
                            for y in DOWN:
                                if y in combination:
                                    assert d in self.sure_candidates_by_cross_row[y]
                                    if d in self[x, y].digits:
                                        assert d in self[x, y].sure_candidates_by_row
                                elif d in self[x, y].digits:
                                    self[x, y].can_not_be(d)
                                    hit = True

                        if hit:
                            # Count the compartments.
                            compartments_found = list()
                            for x in d_sure_union:
                                for compartment in self.compartments_by_col[x]:
                                    for y in combination:
                                        if self[x, y] in compartment and compartment not in compartments_found:
                                            compartments_found.append(compartment)
                            # If the hits are all in the same compartments then they become sure candidates.
                            if len(compartments_found) == r:
                                for x in d_sure_union:
                                    for y in combination:
                                        if d in self[x, y].digits:
                                            self[x, y].sure_candidates_by_col.add(d)
                                            self.sure_candidates_by_cross_col[x].add(d)
                            return hit
            return hit

        for d in ALL:
            if _sea_creatures_by_row(d):
                break

    def sea_creatures_by_col(self):
        def _sea_creatures_by_col(d):
            hit = False
            d_sure_candidates = { }
            for x in ACROSS:
                candidates = set([y for y in DOWN if self[x, y].is_unknown() and d in self[x, y].sure_candidates_by_col])
                if candidates:
                    d_sure_candidates[x] = candidates

            # ??? Is it better to search from large to small?
            for r in xrange(2, len(d_sure_candidates) + 1):
                for combination in combinations(d_sure_candidates, r):
                    # Merge the combinations
                    d_sure_union = set()
                    for c in combination:
                        d_sure_union.update(d_sure_candidates[c])
                    if len(d_sure_union) == r:
                        # We have a sea creature
                        # We can remove 'd' from all the other rows not included this combination that ..
                        # ... have 'd's in the union row.
                        for y in d_sure_union:
                            self.sure_candidates_by_cross_row[y].add(d)
                            for x in ACROSS:
                                if x in combination:
                                    assert d in self.sure_candidates_by_cross_col[x]
                                    if d in self[x, y].digits:
                                        assert d in self[x, y].sure_candidates_by_col
                                elif d in self[x, y].digits:
                                    self[x, y].can_not_be(d)
                                    hit = True

                        if hit:
                            # Count the compartments.
                            compartments_found = list()
                            for y in d_sure_union:
                                for compartment in self.compartments_by_row[y]:
                                    for x in combination:
                                        if self[x, y] in compartment and compartment not in compartments_found:
                                            compartments_found.append(compartment)
                            # If the hits are all in the same compartments then they become sure candidates.
                            if len(compartments_found) == r:
                                for y in d_sure_union:
                                    for x in combination:
                                        if d in self[x, y].digits:
                                            self[x, y].sure_candidates_by_row.add(d)
                                            self.sure_candidates_by_cross_row[y].add(d)
                            return hit
            return hit

        for d in ALL:
            if _sea_creatures_by_col(d):
                break

    def sea_creatures_by_cross_row(self):
        def _sea_creatures_by_cross_row(d):
            hit = False
            d_sure_candidates = { }
            for y in DOWN:
                if d in self.sure_candidates_by_cross_row[y]:
                    candidates = set([x for x in ACROSS if d in self[x, y].digits])
                    if candidates:
                        d_sure_candidates[y] = candidates

            # ??? Is it better to search from large to small?
            for r in xrange(2, len(d_sure_candidates) + 1):
                for combination in combinations(d_sure_candidates, r):
                    # Merge the combinations
                    d_sure_union = set()
                    for c in combination:
                        d_sure_union.update(d_sure_candidates[c])
                    if len(d_sure_union) == r:
                        # We have a sea creature
                        # We can remove 'd' from all the other rows not included this combination that ..
                        # ... have 'd's in the union row.
                        for x in d_sure_union:
                            for y in DOWN:
                                if y not in combination:
                                    if d in self[x, y].digits:
                                        self[x, y].can_not_be(d)
                                        hit = True

                        if hit:
                            # Count the compartments.
                            compartments_found = list()
                            for x in d_sure_union:
                                for compartment in self.compartments_by_col[x]:
                                    for y in combination:
                                        if self[x, y] in compartment and compartment not in compartments_found:
                                            compartments_found.append(compartment)
                            # If the hits are all in the same compartments then they become sure candidates.
                            if len(compartments_found) == r:
                                for x in d_sure_union:
                                    for y in combination:
                                        if d in self[x, y].digits:
                                            self[x, y].sure_candidates_by_col.add(d)
                                            self.sure_candidates_by_cross_col[x].add(d)
                            return hit
            return hit

        for d in ALL:
            if _sea_creatures_by_cross_row(d):
                break

    def sea_creatures_by_cross_col(self):
        def _sea_creatures_by_cross_col(d):
            hit = False
            d_sure_candidates = { }
            for x in ACROSS:
                if d in self.sure_candidates_by_cross_col[x]:
                    candidates = set([y for y in DOWN if d in self[x, y].digits])
                    if candidates:
                        d_sure_candidates[x] = candidates

            # ??? Is it better to search from large to small?
            for r in xrange(2, len(d_sure_candidates) + 1):
                for combination in combinations(d_sure_candidates, r):
                    # Merge the combinations
                    d_sure_union = set()
                    for c in combination:
                        d_sure_union.update(d_sure_candidates[c])
                    if len(d_sure_union) == r:
                        # We have a sea creature
                        # We can remove 'd' from all the other rows not included this combination that ..
                        # ... have 'd's in the union row.
                        for y in d_sure_union:
                            for x in ACROSS:
                                if x not in combination:
                                    if d in self[x, y].digits:
                                        self[x, y].can_not_be(d)
                                        hit = True

                        if hit:
                            # Count the compartments.
                            compartments_found = list()
                            for y in d_sure_union:
                                for compartment in self.compartments_by_row[y]:
                                    for x in combination:
                                        if self[x, y] in compartment and compartment not in compartments_found:
                                            compartments_found.append(compartment)
                            # If the hits are all in the same compartments then they become sure candidates.
                            if len(compartments_found) == r:
                                for y in d_sure_union:
                                    for x in combination:
                                        if d in self[x, y].digits:
                                            self[x, y].sure_candidates_by_row.add(d)
                                            self.sure_candidates_by_cross_row[y].add(d)
                            return hit
            return hit

        for d in ALL:
            if _sea_creatures_by_cross_col(d):
                break

    def settis_rule(self):
        def _count_sure_candidates_by_row(d):
            sc = { 'yes': set(), 'no': set(), 'maybe': set() }
            for y in DOWN:
                no = True
                for x in ACROSS:
                    c = self[x, y]
                    # If any of the cells is 'd' we can flag it as a 'yes'.
                    if c.is_known() and c.value() == d:
                        sc['yes'].add(y)
                        break
                    elif d in c.digits:
                        no = False
                else:
                    # If we didn't see 'd' then flag it as 'no'
                    if no:
                        sc['no'].add(y)
                    else:
                        # This tests for sc by compartment
                        if d in self.sure_candidates_by_cross_row[y]:
                            sc['yes'].add(y)
                        else:
                            sc['maybe'].add(y)

            assert len(sc['yes']) + len(sc['no']) + len(sc['maybe']) == 9
            return sc

        def _count_sure_candidates_by_col(d):
            sc = { 'yes': set(), 'no': set(), 'maybe': set() }
            for x in ACROSS:
                no = True
                for y in DOWN:
                    c = self[x, y]
                    # If any of the cells is 'd' we can flag it as a 'yes'.
                    if c.is_known() and c.value() == d:
                        sc['yes'].add(x)
                        break
                    elif d in c.digits:
                        no = False
                else:
                    # If we didn't see 'd' then flag it as 'no'
                    if no:
                        sc['no'].add(x)
                    else:
                        # This tests for sc by compartment
                        if d in self.sure_candidates_by_cross_col[x]:
                            sc['yes'].add(x)
                        else:
                            sc['maybe'].add(x)

            assert len(sc['yes']) + len(sc['no']) + len(sc['maybe']) == 9
            return sc

        def _settis_rule(d):
            hit = False

            sc_by_row = _count_sure_candidates_by_row(d)
            sc_by_col = _count_sure_candidates_by_col(d)
            row_yes, row_maybe, row_no = sc_by_row['yes'], sc_by_row['maybe'], sc_by_row['no']
            col_yes, col_maybe, col_no = sc_by_col['yes'], sc_by_col['maybe'], sc_by_col['no']

            if False:
                print('d:{} row[y{}-m{}-n{}] col[y{}-m{}-n{}]'.format(d,
                    len(row_yes), len(row_maybe), len(row_no),
                    len(col_yes), len(col_maybe), len(col_no)))
                print('rY:', row_yes)
                print('rM:', row_maybe)
                print('rN:', row_no)
                print('cY:', col_yes)
                print('cM:', col_maybe)
                print('cN:', col_no)
            if False:
                for x in ACROSS:
                    print('col sc:', x, self.sure_candidates_by_cross_col[x])
                for y in DOWN:
                    print('row sc:', y, self.sure_candidates_by_cross_row[y])

            # Early out if both are known.
            if len(row_maybe) == 0 and len(col_maybe) == 0:
                assert len(row_yes) == len(col_yes)
                assert len(row_no) == len(col_no)
                return hit

            # If the #maybe in the rows is 0, then ...
            # ... we know the #yes col must equal #yes row, and ...
            # ... we know the #no col must equal #no row.
            if len(row_maybe) == 0:
                # If rY == cY then we know all the cM should be cN.
                if len(row_yes) == len(col_yes):
                    for x in col_maybe:
                        assert d not in self.sure_candidates_by_cross_col[x]
                        for y in DOWN:
                            assert d not in self[x, y].sure_candidates_by_col
                            self[x, y].can_not_be(d)
                # If rN == cN then we know all the cM should be cY.
                elif len(row_no) == len(col_no):
                    for x in col_maybe:
                        d_compartment_count = 0
                        for compartment in self.compartments_by_col[x]:
                            for c in compartment:
                                if d in c.digits:
                                    d_compartment_count += 1
                                    break
                        if d_compartment_count == 1:
                            for y in DOWN:
                                if (d in self[x, y].digits) and (d not in self[x, y].sure_candidates_by_col):
                                    self[x, y].sure_candidates_by_col.add(d)
                                    hit = True
                        if d not in self.sure_candidates_by_cross_col[x]:
                            self.sure_candidates_by_cross_col[x].add(d)
                            hit = True

            # If the #maybe in the coll is 0, then ...
            # ... we know the #yes col must equal #yes row, and ...
            # ... we know the #no col must equal #no row.
            if len(col_maybe) == 0:
                # If rY == cY then we know all the cM should be cN.
                if len(col_yes) == len(row_yes):
                    for y in row_maybe:
                        assert d not in self.sure_candidates_by_cross_row[y]
                        for x in ACROSS:
                            assert d not in self[x, y].sure_candidates_by_row
                            self[x, y].can_not_be(d)
                # If rN == cN then we know all the cM should be cY.
                elif len(row_no) == len(col_no):
                    for y in row_maybe:
                        d_compartment_count = 0
                        for compartment in self.compartments_by_row[y]:
                            for c in compartment:
                                if d in c.digits:
                                    d_compartment_count += 1
                                    break
                        if d_compartment_count == 1:
                            for x in ACROSS:
                                if (d in self[x, y].digits) and (d not in self[x, y].sure_candidates_by_row):
                                    self[x, y].sure_candidates_by_row.add(d)
                                    hit = True
                        if d not in self.sure_candidates_by_cross_row[y]:
                            self.sure_candidates_by_cross_row[y].add(d)
                            hit = True

            return hit

        return any(map(_settis_rule, ALL))

    def unique_rectangle_rule(self):
        for (x, y), c in self.iteritems():
            if len(c.digits) == 2:
                for dy in DOWN:
                    if dy == y:
                        continue
                    d = self[x, dy]
                    if len(d.digits) == 2 and c.digits == d.digits:
                        # Pair
                        for dx in ACROSS:
                            if dx == x:
                                continue
                            d1, d2 = self[dx, y], self[dx, dy]
                            if d1.is_unknown() and d2.is_unknown():
                                for d in c.digits:
                                    if d not in d1.digits or d not in d2.digits:
                                        break
                                else:
                                    if len(d1.digits) == 2:
                                        d2.can_not_be(d1.digits)
                                    elif len(d2.digits) == 2:
                                        d1.can_not_be(d2.digits)
                                    elif len(d1.digits) == 3 and len(d2.digits) == 3 and d1.digits == d2.digits:
                                        digits = set(d1.digits)
                                        digits.difference_update(c.digits)
                                        for other_y in DOWN:
                                            if other_y == y or other_y == dy:
                                                continue
                                            self[dx, other_y].can_not_be(digits)

                for dx in ACROSS:
                    if dx == x:
                        continue
                    d = self[dx, y]
                    if len(d.digits) == 2 and c.digits == d.digits:
                        # Pair
                        for dy in DOWN:
                            if dy == y:
                                continue
                            d1, d2 = self[x, dy], self[dx, dy]
                            if d1.is_unknown() and d2.is_unknown():
                                for d in c.digits:
                                    if d not in d1.digits or d not in d2.digits:
                                        break
                                else:
                                    if len(d1.digits) == 2:
                                        d2.can_not_be(d1.digits)
                                    elif len(d2.digits) == 2:
                                        d1.can_not_be(d2.digits)
                                    elif len(d1.digits) == 3 and len(d2.digits) == 3 and d1.digits == d2.digits:
                                        digits = set(d1.digits)
                                        digits.difference_update(c.digits)
                                        for other_x in ACROSS:
                                            if other_x == x or other_x == dx:
                                                continue
                                            self[other_x, dy].can_not_be(digits)

    def unique_solution_constraint(self):
        # This implementation solves the test case - but isn't smart enough to solve many other cases.
        # Needs a better implementation.

        # First we search for compartments that are isolated.
        candidates = [ ]
        for _, compartment in self._iter_compartments_by_row():
            if len(compartment) == 1:
                cell = compartment[0]
                if len(cell.digits) == 2:
                    candidates.append(cell)
        singles = [ ]
        for _, compartment in self._iter_compartments_by_col():
            if len(compartment) == 1:
                cell = compartment[0]
                if cell in candidates:
                    singles.append(cell)
        if singles:
            # This is a list of the isolated compartments
            for (x, y), c in self.iteritems():
                if c in singles:
                    # We want to find a digit that is isolated
                    compartments_with_digit = DefaultDict(list)
                    for d in c.digits:
                        for compartment in self.compartments_by_row[y]:
                            if c not in compartment:
                                for dc in compartment:
                                    if d in dc.digits:
                                        compartments_with_digit[d].append( (compartment, Cell.get_sc_by_row) )
                                        break
                        for compartment in self.compartments_by_col[x]:
                            if c not in compartment:
                                for dc in compartment:
                                    if d in dc.digits:
                                        compartments_with_digit[d].append( (compartment, Cell.get_sc_by_col) )
                                        break
                    # What if two compartments touch this digit?
                    if len(compartments_with_digit) == 1:
                        for digit, pack in compartments_with_digit.iteritems():
                            compartment, sc_fn = pack[0]
                            c.can_not_be(digit)
                            for dc in compartment:
                                if digit in dc.digits:
                                    sc_fn(dc).add(digit)

    def y_wing(self):
        for (x, y), c in self.iteritems():
            if len(c.digits) == 2:
                c0, c1 = c.digits[0], c.digits[1]
                # This might be a candidate for BLUE.
                for (dx, dy), dc in self._iter_all_but(x, y):
                    if dc.is_unknown() and \
                        (len(self[dx, y].digits) == 2) and \
                        (len(self[x, dy].digits) == 2) and \
                        ( ((c0 in self[dx, y].digits) and (c1 in self[x, dy].digits)) or \
                          ((c1 in self[dx, y].digits) and (c0 in self[x, dy].digits)) ):
                        z0 = set(self[dx, y].digits).difference(c.digits)
                        z1 = set(self[x, dy].digits).difference(c.digits)
                        if len(z0) == 1 and z0 == z1:
                            dc.can_not_be(z0.pop())

    def sure_candidate_upgrade_row(self):
        return any(sure_candidate_upgrade_by_cells(self.compartments_by_row[y],
                                                   self.sure_candidates_by_cross_row[y],
                                                   Cell.get_sc_by_row) for y in DOWN)

    def sure_candidate_upgrade_col(self):
        return any(sure_candidate_upgrade_by_cells(self.compartments_by_col[x],
                                                   self.sure_candidates_by_cross_col[x],
                                                   Cell.get_sc_by_col) for x in ACROSS)

    def sure_candidate_range_check_row(self):
        for _, compartment in self._iter_compartments_by_row():
            sure_candidate_range_check_by_cells(compartment, Cell.get_sc_by_row)

    def sure_candidate_range_check_col(self):
        for _, compartment in self._iter_compartments_by_col():
            sure_candidate_range_check_by_cells(compartment, Cell.get_sc_by_col)

    def chain_contradiction(self):
        def _solve(b):
            completeness = b._completeness()
            while completeness != 729:
                for s in Board.steps[:-1]:
                    hit = s(board)
                    board._valid()
                    c = board._completeness()
                    if hit or completeness != c:
                        completeness = c
                        break
                else:
                    if board._completeness() == completeness:
                        board._valid()
                        return False
            else:
                board._valid()
                return True

        for digits_len in xrange(2, self.chain_length + 1):
            for (x, y), cell in self.iteritems():
                digits = cell.digits
                if len(digits) == digits_len:
                    for d in digits:
                        try:
                            board = deepcopy(self)
                            #print('Considering', d, 'in', x, y)
                            board[x, y].value_is(d)
                            if _solve(b):
                                cell.value_is(d)
                                return
                        except:
                            # We found a contradiction.
                            cell.can_not_be(d)
                            return

    steps = [
        remove_used_digits,             # checked
        compartment_range_check_by_row, # checked
        compartment_range_check_by_col, # checked
        singles_by_row,
        singles_by_col,
        sure_candidates_by_row,         # checked
        sure_candidates_by_col,         # checked
        stranded_digits_by_row,         # checked
        stranded_digits_by_col,         # checked
        bridging_digits_by_row,
        bridging_digits_by_col,
        split_compartments_by_row,
        split_compartments_by_col,
        mind_the_gap_by_row,
        mind_the_gap_by_col,
        mind_the_bridging_gap_by_row,
        mind_the_bridging_gap_by_col,
        naked_groups_by_col,
        naked_groups_by_row,
        hidden_group_by_row,
        hidden_group_by_col,
        hidden_group_by_cross_row,
        hidden_group_by_cross_col,
        # TODO - Locked Compartments
        sea_creatures_by_row,
        sea_creatures_by_col,
        sea_creatures_by_cross_row,
        sea_creatures_by_cross_col,
        settis_rule,
        unique_rectangle_rule,
        unique_solution_constraint,
        y_wing,
        sure_candidate_upgrade_row,
        sure_candidate_upgrade_col,
        sure_candidate_range_check_row,
        sure_candidate_range_check_col,
        stranded_by_bridge_by_row,
        stranded_by_bridge_by_col,
        chain_contradiction
    ]

    def solve(self, title, steps=steps, verbose=False, debug=False, sure=False):
        def _dump():
            if verbose or debug:
                print(self._to_string(sure_candidates=sure))

        if debug:
            print(self)

        iteration = 0
        completeness = self._completeness()
        while completeness != 729:
            for s in steps:
                hit = s(self)
                iteration += 1

                c = self._completeness()
                if hit or completeness != c:
                    self.counts[s.__name__] += c - completeness
                    self.hits[s.__name__] += 1
                    if debug:
                        if s.__name__ in [ 'remove_used_digits',
                                           'sure_candidates_by_row',
                                           'sure_candidates_by_col',
                                           'compartment_range_check_by_row',
                                           'compartment_range_check_by_col',
                                           'stranded_digits' ]:
                            _hit(s.__name__)
                        else:
                            _caution(s.__name__)
                        _dump()
                        _comment('Iteration {}: {:.2%} ({} of 729)'.format(iteration, float(c) / 729, c))
                        # Check if there are any errors
                        self._valid()
                    completeness = c
                    break
                else:
                    if debug:
                        _miss(s.__name__)

            else:
                if self._completeness() == completeness:
                    _fail('{:<12} [{:>4}] [{:>4} of {:2}] [{:3} of 729]'.format(
                        name, iteration, len(self.counts), len(steps), completeness))
                    self._clear_removed()
                    _dump()
                    self._valid()
                    return False
        else:
            _pass('{:<12} [{:>4}] [{:>4} of {:2}]'.format(name, iteration, len(self.counts), len(steps)))
            self._clear_removed()
            if verbose:
                print(self)
            self._valid()
            return True

######################################################################################################################
    # Unit tests

def test(fns, test, result, exit_on_error=True, verbose=True):
    def _test(fn, t, r):
        board = Board(t)
        # Run the test a few times, incase it hits multiple cases.
        for _ in xrange(9):
            fn(board)
        if board == r:
            if verbose:
                _pass('Test {}'.format(fn.__name__))
        else:
            import inspect
            line_number = inspect.getouterframes(inspect.currentframe())[2][2]
            msg = 'Test {} line #{}'.format(fn.__name__, line_number)
            if exit_on_error:
                _fail(msg)
                print(board._to_string(True))
                exit()
            else:
                _todo(msg)

    if not isinstance(fns, list):
        fns = [fns, fns]

    _test(fns[0], test, result)
    _test(fns[1], zip(*test), zip(*result))

def tests():
    a = '123456789'

    # pg 8. Sure Candidates
    test( [Board.sure_candidates_by_row, Board.sure_candidates_by_col],
          [ ['2345678', '345678', '45678', '234567', '#', a, a, a],
            ['123456', '123456', '123456', '123456', '#', a, a, a],
            [a, a, a, a, a, a, a, '#', a] ],
          [ ['2345678', '345678', '45678',  '234567', '#', '12346789', '12346789', '12346789'       ],
            ['123456', '123456',  '123456', '123456', '#', '56789',    '56789',    '56789'          ],
            [a,         a,        a,        a,        a,   a,          a,          '#',       '1289'] ] )
    # bonus. Sure Candidates
    test( [Board.sure_candidates_by_row, Board.sure_candidates_by_col],
          [['#', '6789', '6789', '#', '2345678', '12345', '12345678', '123456789', '1345678']],
          [['#', '6789', '6789', '#', '234567',  '12345', '1234567',  '1234567',   '134567']] )
    test( [Board.sure_candidates_by_row, Board.sure_candidates_by_col],
          [['12456', '8', '1235679', '2345679', '12345679', '12345679', '#', '12457', '#']],
          [['12456', '8', '1235679', '2345679', '12345679', '12345679', '#', '127', '#']] )
    test( [Board.sure_candidates_by_row, Board.sure_candidates_by_col],
          [['i', '345678', '123456', '1247', '134568', '#', '3456', '568', '34567']],
          [['i', '345',    '12345',  '124',  '1345',   '#', '56',   '568', '567'  ]] )
    test( [Board.sure_candidates_by_row, Board.sure_candidates_by_col],
          [['123567', '123567', '123567', '#', a, a, a]],
          [['123567', '123567', '123567', '#', a, a, a]] )
    # pg 9. Singles
    test( [Board.singles_by_row, Board.singles_by_col],
          [['358', '357', '456', '3457']], [['358', '357', '6', '3457']])
    # pg 10. Compartment Range Checks
    test( [Board.compartment_range_check_by_row, Board.compartment_range_check_by_col],
          [['234567', '56789', '1235678', '#'], [a, a, '4', a]],
          [['34567', '56789', '35678', '#'], ['1234567', '1234567', '4', '1234567']] )
    # pg 11. Compartment Range Checks
    test( [Board.compartment_range_check_by_row, Board.compartment_range_check_by_col],
          [ ['56789', '56789', '1234567', '234567', '#'],
            ['56789', '56789', '56789', a, a],
            ['5689', '5789', '6789', a, a] ],
          [ ['56789', '56789', '34567', '34567', '#'],
            ['56789', '56789', '56789', '3456789', '3456789'],
            ['5689', '5789', '6789', '3456789', '3456789'] ] )
    # bonus. Compartment Range Checks
    test( [Board.compartment_range_check_by_row, Board.compartment_range_check_by_col],
          [['12456', '8', '123567', '2345679', '12345679', '12345679', '#', '127', '#']],
          [['456', '8', '3567', '345679', '345679', '345679', '#', '127', '#']] )
    # pg 12. Stranded Digits
    test( [Board.stranded_digits_by_row, Board.stranded_digits_by_col],
          [['1245679', '12679', '1245679', 'c', '8']], [['4567', '67', '4567', '#', '8']])
    # pg 13. Stranded Digits - Bridging Digits
    test( [Board.bridging_digits_by_row, Board.bridging_digits_by_col],
          [['13456', '1234568', '145678', '134568']], [['13456', '234568', '14567', '134568']] )
    test( [Board.bridging_digits_by_row, Board.bridging_digits_by_col],
          [['13679', '1234689']], [['1379', '2468']] )
    test( [Board.bridging_digits_by_row, Board.bridging_digits_by_col],
          [['1', '3', '23']], [['1', '3', '2']] )
    # bonus. Stranded Digits - Bridging Digits
    test( [Board.bridging_digits_by_row, Board.bridging_digits_by_col],
          [['568', '5689', '7']], [['568', '5689', '7']] )
    test( [Board.bridging_digits_by_row, Board.bridging_digits_by_col],
          [['68', '7', '568']], [['68', '7', '568']] )
    test( [Board.bridging_digits_by_row, Board.bridging_digits_by_col],
          [['124678', '5', '234678', '#', '12678', '12367', 'i', '12367', '1234']],
          [['124678', '5', '234678', '#', '12678', '12367', 'i', '123', '1234']] )
    # bonus. Better stranded + bridging digits
    test( [Board.stranded_by_bridge_by_row, Board.stranded_by_bridge_by_col],
          [['347', '2347', '34568', '1245']],
          [['347', '2347', '3456',  '1245']] )
    test( [Board.stranded_by_bridge_by_row, Board.stranded_by_bridge_by_col],
          [['46', '1235789', '1235789', '1235789']],
          [['46', '1235789', '1235789', '1235789']] )
    test( [Board.stranded_by_bridge_by_row, Board.stranded_by_bridge_by_col],
          [['17', '23458', '69', '23458', '23458', '23458']],
          [['17', '23458', '6',  '23458', '23458', '23458']] )
    # pg 14. + 15. Split Compartments
    test( [Board.split_compartments_by_row, Board.split_compartments_by_col],
          [['23678', '124678', '236789', '123467']],
          [['23678', '14678',  '239',    '1467'  ]] )
    test( [Board.split_compartments_by_row, Board.split_compartments_by_col],
          [['134679',  '12346789', '134679',  '134679']],
          [['134679',  '28',       '134679',  '134679']] )
    # pg 16. Mind the Gap
    test( [Board.mind_the_gap_by_row, Board.mind_the_gap_by_col],
          [['123456', '345678', '27', '123457']], [['13456', '34568', '27', '1345']])
    # pg 17. Mind the Gap
    test( [Board.mind_the_gap_by_row, Board.mind_the_gap_by_col],
          [ ['123456', '345678', '237', '123457'],
            ['123456', '345678', '2378', '123457'] ],
          [ ['123456', '34568', '237', '12345'],
            ['123456', '345678', '2378', '123457'] ] )
    # pg 18. Mind the Gap
    test( [Board.mind_the_bridging_gap_by_row, Board.mind_the_bridging_gap_by_col],
          [['35', '2345678', '58', '123457', '13456']], [['35', '234678', '58', '12347', '1346']])
    # pg 19. Naked Pair
    test( [Board.naked_groups_by_row, Board.naked_groups_by_col],
          [['345679', '45', '2345689',  '45']],
          [['3679', '45', '23689', '45']] )
    # pg 20. Naked Triple/Quadruple/Qunituple
    test( [Board.naked_groups_by_row, Board.naked_groups_by_col],
          [ ['23456789', '467', '1235789', '47', '34789', '467', '145689'],
            ['23456789', '3467', '1235789', '3467', '3467', '3467', '145689'],
            ['34567', '467', '23456789', '367', '3456', '34567', '1245689'] ],
          [ ['23589', '467', '123589', '47', '389', '467', '1589'],
            ['2589', '3467', '12589', '3467', '3467', '3467', '1589'],
            ['34567', '467', '289', '367', '3456', '34567', '1289'] ] )
    # bonus. Naked Groups
    test( [Board.naked_groups_by_row, Board.naked_groups_by_col],
          [['7', '1458', '146', '2', '14', '468', '4568', '14568', 'i']],
          [['7', '1458', '146', '2', '14', '468', '4568', '14568', 'i']] )
    # pg 21. Cross-compartment Locked Sets
    test( [Board.naked_groups_by_row, Board.naked_groups_by_col],
          [['1234567', '345', '1234567', '#', '2456', '345', '234567', '#', '34']],
          [['1267', '345', '1267', '#', '26', '345', '267', '#', '34']] )
    # pg 22. Hidden Pair
    test( [Board.hidden_group_by_row, Board.hidden_group_by_col],
          [['34568', '3678', '4578', '368', '367']],
          [['45', '3678', '45', '368', '367']] )
    # pg 23. Hidden Triple/Quadruple/Qunituple
    test( [Board.hidden_group_by_row, Board.hidden_group_by_col],
          [ ['34569', '12358', '1356789', '12589', '123589', '1234567', '1589', '#'],
            ['34569', '12589', '1356789', '12589', '1259', '1234567', '134589', '#'],
            ['1479', '1245678', '1235679', '1479', '1345679', '1479', '1234689', '124568'] ],
          [ ['46', '12358', '67', '12589', '123589', '467', '1589', '#'],
            ['346', '12589', '367', '12589', '1259', '3467', '34', '#'],
            ['1479', '2568', '2356', '1479', '356', '1479', '2368', '2568'] ] )
    # pg 24. Cross-compartment Hidden Sets
    test( [Board.hidden_group_by_cross_row, Board.hidden_group_by_cross_col],
          [['2569', '1234678', '12569', '1234578', '#', '12569', '234578', '2569', '1234678']],
          [['2569', '3478',    '12569', '3478',    '#', '12569', '3478',   '2569', '3478']] )
    # pg 25, 26, 27. Locked Compartments
    # TODO
    # pg 28, 29. X-Wing
    test( [Board.sea_creatures_by_col, Board.sea_creatures_by_row],
          # col and row deliberately swapped to fit test case
          [ ['245678',  '1456',  '12',    '134569'  ],
            ['12356',   '12456', '1245',  '134569'  ],
            ['345689',  '2356',  '1234',  '123678'  ],
            ['124569',  '12346', '2345',  a         ],
            ['123',     '12',    '#',     '3456789' ],
            ['1289',    '#',     '56789', '1245678' ],
            ['124678',  '6789',  '56789', '12479'   ],
            ['134679',  '6789',  '56789', '1234789' ],
            ['3456789', '6789',  '56789', '1234789' ] ],
          [ ['245678',  '1456',  '12',    '134569'  ],
            ['12356',   '12456', '1245',  '134569'  ],
            ['45689',   '2356',  '1234',  '12678'   ],
            ['124569',  '12346', '2345',  '12456789'],
            ['123',     '12',    '#',     '3456789' ],
            ['1289',    '#',     '56789', '1245678' ],
            ['124678',  '6789',  '56789', '12479'   ],
            ['134679',  '6789',  '56789', '1234789' ],
            ['3456789', '6789',  '56789', '1234789' ] ] )
    # pg 30. X-Wing
    test( [Board.sea_creatures_by_row, Board.sea_creatures_by_col],
          [ ['79',   '8',    '6',    '579',   '579',     'b',    '#',     '34',   '34'     ],
            ['679',  '79',   '8',    '5679',  '5679',    '#',    '4',     '23',   '23'     ],
            ['89',   '#',    '479',  '6789',  '3',       '489',  '12789', '124',  '5'      ],
            ['#',    '6',    '457',  '57',    '1247',    '3',    '1257',  'h',    '179'    ],
            ['#',    '1247', '4579', '56789', '1245679', '4589', '3',     '4567', '1246789'],
            ['123',  '12',   '#',    'd',     '69',      '7',    '589',   '56',   '689'    ],
            ['124',  '3',    '124',  '#',     '8',       '459',  '579',   '4567', '4679'   ],
            ['2345', '2457', '234',  '1',     '2457',    '6',    '257',   '#',    '#'      ],
            ['1345', '145',  '134',  '2',     '#',       '589',  '6',     '79',   '89'     ] ],
          [ ['79',   '8',    '6',    '579',   '579',     'b',    '#',     '34',   '34'     ],
            ['679',  '79',   '8',    '579',   '579',     '#',    '4',     '23',   '23'     ],
            ['89',   '#',    '479',  '6789',  '3',       '489',  '12789', '124',  '5'      ],
            ['#',    '6',    '457',  '7',     '1247',    '3',    '1257',  'h',    '179'    ],
            ['#',    '1247', '4579', '789',   '124679',  '4589', '3',     '4567', '1246789'],
            ['12',   '12',   '#',    'd',     '69',      '7',    '589',   '56',   '689'    ],
            ['124',  '3',    '124',  '#',     '8',       '459',  '579',   '4567', '4679'   ],
            ['2345', '2457', '234',  '1',     '247',     '6',    '27',    '#',    '#'      ],
            ['1345', '145',  '134',  '2',     '#',       '89',   '6',     '79',   '89'     ] ] )
    # pg 31. X-Wing
    test( [Board.sea_creatures_by_row, Board.sea_creatures_by_col],
          [ ['457',    '456',     '467',      '#',      a],
            ['356789', '13479',   '456789',   '45678',  a],
            ['345689', '1245689', '123568',   '4567',   a],
            ['3456',   '356',     '346',      '#',      a],
            ['#',      '1234567', '12456789', '12567',  a],
            ['12458',  '#',       '123567',   '123579', a] ],
          [ ['457',    '456',     '467',      '#',      a],
            ['36789',  '13479',   '456789',   '45678',  a],
            ['34689',  '124689',  '123568',   '4567',   a],
            ['3456',   '356',     '346',      '#',      a],
            ['#',      '123467',  '12456789', '12567',  a],
            ['1248',   '#',       '123567',   '123579', a] ] )
    # pg 32. Swordfish
    test( [Board.sea_creatures_by_col, Board.sea_creatures_by_row],
          # col and row deliberately swapped to fit test case
          [ ['12356789', '1245',  '234',    '125678',  '2345', '13456789'],
            ['1256789',  '12345', '23',     '1234679', '245',  '12345679'],
            ['125679',   '12345', '#',      '134567',  '2345', '125689'  ],
            ['1356',     '#',     '123456', '2356',    '#',    '245689'  ] ],
          [ ['1256789',  '1245',  '234',    '125678',  '2345', '1456789' ],
            ['1256789',  '12345', '23',     '124679',  '245',  '1245679' ],
            ['125679',   '12345', '#',      '14567',   '2345', '125689'  ],
            ['1356',     '#',     '123456', '2356',    '#',    '245689'  ] ] )
    # pg 33, 34. Jellyfish
    test( [Board.sea_creatures_by_col, Board.sea_creatures_by_row],
          # col and row deliberately swapped to fit test case
          [ ['1245',  '235679',  '123567',  '345',   '123456789', '3467' ],
            ['345',   '345679',  '1234567', '34',    '123456789', '3578' ],
            ['1234',  '1234',    '123456',  '#',     '123456789', '4568' ],
            ['12345', '345679',  '123467',  '56789', '123456789', '4567' ],
            ['#',     '2345789', '#',       '56789', '123456789', '35678'],
            ['5678',  '45679',   '5689',    '56789', '456789',    '#'    ] ],
          [ ['1245',  '235679',  '123567',  '345',   '12356789',  '3467' ],
            ['345',   '35679',   '1234567', '34',    '12356789',  '3578' ],
            ['1234',  '123',     '123456',  '#',     '12356789',  '4568' ],
            ['12345', '35679',   '123467',  '56789', '12356789',  '4567' ],
            ['#',     '2345789', '#',       '56789', '123456789', '35678'],
            ['5678',  '45679',   '5689',    '56789', '456789',    '#'    ] ] )
    # pg 35, 36. Starfish, Sea Creatures
    test( [Board.sea_creatures_by_row, Board.sea_creatures_by_col],
          [ ['568',    '7',        '58',      '568',    '#',       '123',     '1234',   '124',     '1234'  ],
            ['578',    '58',       '6',       '578',    '#',       '123',     '1234',   '124',     '1234'  ],
            ['45789',  '45689',    '4589',    '45678',  '45679',   '#',       '1234',   '124',     '1234'  ],
            ['45679',  '345689',   '123459',  '124679', '1256789', '3489',    '#',      '123789',  '12789' ],
            ['235689', '1456',     '124579',  '4568',   '12347',   '46789',   '478',    '12489',   '123478'],
            [a,        '12345689', '12345789', a,       a,         '3456789', '456789', '12456789', a      ] ],
          [ ['568',      '7',       '58',      '568',      '#',        '123',     '1234',   '124',      '1234'    ],
            ['578',      '58',      '6',       '578',      '#',        '123',     '1234',   '124',      '1234'    ],
            ['45789',    '45689',   '4589',    '45678',    '45679',    '#',       '1234',   '124',      '1234'    ],
            ['45679',    '345689',  '123459',  '124679',   '1256789',  '489',     '#',      '123789',   '12789'   ],
            ['235689',   '1456',    '124579',  '4568',     '12347',    '46789',   '478',    '12489',    '12478'   ],
            ['12346789', '1234689', '1234789', '12346789', '12346789', '456789',  '456789', '12456789', '12456789'] ] )
    # pg 37. Cross-compartment Sea Creatures
    test( [Board.sea_creatures_by_cross_col, Board.sea_creatures_by_cross_row],
          # col and row deliberately swapped to fit test case
          [ ['134',  '1345',  '1356789' ],
            ['1234', '12345', '1234568' ],
            ['#',    '1345',  '12345689'],
            ['1234', '12345', '12345679'],
            ['134',  '#',     '12345789'],
            ['#',    '56789', '12346789'] ],
          [ ['134',  '1345',  '1356789' ],
            ['1234', '12345', '134568'  ],
            ['#',    '1345',  '12345689'],
            ['1234', '12345', '1345679' ],
            ['134',  '#',     '12345789'],
            ['#',    '56789', '12346789'] ] )
    # pg 38, 39, 40 - Setti's Rule
    test( Board.settis_rule,
          [ ['a',      'b',     '#',       '78',    '78',   '9',       '#',     '#',        '#'      ],
            ['245678', '14568', '125678',  '9',     '678',  '125678',  '3',     '1245678',  '124567' ],
            ['289',    '#',     '3',       '2478',  '789',  '12578',   '6',     '124578',   '12457'  ],
            ['289',    '#',     '1256789', '24678', '6789', '1235678', '12489', '12345678', '1234567'],
            ['26789',  '#',     '6789',    '678',   'a',    '4',       '5',     '#',        '2367'   ],
            ['24689',  '7',     '12689',   '5',     '234',  '12368',   '12489', '#',        '12'     ],
            ['3',      '5689',  '125689',  '2468',  '245',  '12568',   '7',     '#',        '12'     ],
            ['256789', '5689',  '4',       '3',     '25',   '125678',  '1289',  '125678',   '12567'  ],
            ['#',      '#',     '#',       '1',     '23',   '23',      '#',     'i',        'h'      ] ],
          [ ['a',      'b',     '#',       '78',    '78',   '9',       '#',     '#',        '#'      ],
            ['245678', '168',   '125678',  '9',     '678',  '125678',  '3',     '12678',    '124567' ],
            ['289',    '#',     '3',       '2478',  '789',  '12578',   '6',     '1278',     '12457'  ],
            ['289',    '#',     '1256789', '24678', '6789', '1235678', '12489', '123678',   '1234567'],
            ['26789',  '#',     '6789',    '678',   'a',    '4',       '5',     '#',        '2367'   ],
            ['24689',  '7',     '12689',   '5',     '234',  '12368',   '12489', '#',        '12'     ],
            ['3',      '689',   '125689',  '2468',  '245',  '12568',   '7',     '#',        '12'     ],
            ['256789', '689',   '4',       '3',     '25',   '125678',  '1289',  '12678',    '12567'  ],
            ['#',      '#',     '#',       '1',     '23',   '23',      '#',     'i',        'h'      ] ] )
    # pg 41. - Setti's Rule
    test( Board.settis_rule,
          [ ['3456', '2',   '9',  '345',  '14567',  '8',    '567',  '14', '467'],
            ['2',    '3',   '#',  '4589', '45789',  '79',   '578',  '6',  '47' ],
            ['569',  'a',   '#',  '7',    '68',     '#',    'd',    '2',  '3'  ],
            ['1',    '45',  '45', '6',    '3',      '2',    '#',    '7',  '8'  ],
            ['4569', '457', '45', '4589', '456789', '567',  'a',    '3',  '2'  ],
            ['7',    '8',   '6',  '#',    '2',      '4',    '3',    '5',  '1'  ],
            ['8',    '9',   'g',  '#',    '146',    '3',    '2',    '14', '5'  ],
            ['45',   '6',   '3',  '2',    '1457',   '157',  '#',    'h',  '9'  ],
            ['3456', '457', '2',  '13',   '145678', '1567', '5678', '9',  '467'] ],
          [ ['3456', '2',   '9',  '345',  '14567',  '8',    '567',  '14', '467'],
            ['2',    '3',   '#',  '4589', '45789',  '79',   '578',  '6',  '47' ],
            ['569',  'a',   '#',  '7',    '68',     '#',    'd',    '2',  '3'  ],
            ['1',    '45',  '45', '6',    '3',      '2',    '#',    '7',  '8'  ],
            ['4569', '457', '45', '4589', '456789', '567',  'a',    '3',  '2'  ],
            ['7',    '8',   '6',  '#',    '2',      '4',    '3',    '5',  '1'  ],
            ['8',    '9',   'g',  '#',    '146',    '3',    '2',    '14', '5'  ],
            ['45',   '6',   '3',  '2',    '1457',   '157',  '#',    'h',  '9'  ],
            ['3456', '457', '2',  '13',   '145678', '1567', '5678', '9',  '467'] ] )
    # pg 42, 43. - Unique Solution Contraint
    test( Board.unique_rectangle_rule,
          [ ['1236789', '45', '45', '1236789'],
            ['1236789', '456', '45', '1236789'],
            ['123456', '1236', '1236', '123456'] ],
          [ ['1236789', '45', '45', '1236789'],
            ['1236789', '6', '45', '1236789'],
            ['123456', '1236', '1236', '123456'] ] )
    test( Board.unique_rectangle_rule,
          [ ['#',       '9',   '8' ],
            ['#',       '#',   '5' ],
            ['456789',  '567', '67'],
            ['3456789', '567', '67'],
            ['#',       '8',   '9' ],
            ['5678',    '567', '#' ] ],
          [ ['#',       '9',   '8' ],
            ['#',       '#',   '5' ],
            ['456789',  '567', '67'],
            ['3456789', '567', '67'],
            ['#',       '8',   '9' ],
            ['5678',    '67',  '#' ] ] )
    # pg 44. - Unique Solution Contraint
    test( [Board.split_compartments_by_col, Board.split_compartments_by_row],
          # col and row deliberately swapped to fit test case
          [ ['134689', '#',  '#',      '3468'],
            ['2349',   '6',  '#',      '7'   ],
            ['3468',   '78', '3478',   '5'   ],
            ['5',      '78', '234789', '3468'] ],
          [ ['134689', '#',  '#',      '3468'],
            ['2349',   '6',  '#',      '7'   ],
            ['3468',   '78', '348',    '5'   ],
            ['5',      '78', '2349',   '3468'] ], False )
    # pg 45. - Unique Solution Contraint
    #test()
    # bonus
    test( Board.unique_solution_constraint,
          [['19', '#', '45678', '3456789', '345789']],
          [['1',  '#', '45678', '3456789', '345789']] )
    # pg 46, 47. - Y-Wing
    test( Board.y_wing,
          [ ['23456789', '23456789', '57',  '23789', '#',       '123456789', '123456789', '123456789'],
            ['12789',    '12789',    '378', '#',     '2345678', '2345678',   '2345678',   '2345678'  ],
            ['6789',     '6789',     '67',  '#',     '123456',  '123456',    '56',        '123456'   ] ],
          [ ['23456789', '23456789', '57',  '23789', '#',       '123456789', '12346789',  '123456789'],
            ['12789',    '12789',    '378', '#',     '2345678', '2345678',   '2345678',   '2345678'  ],
            ['6789',     '6789',     '67',  '#',     '123456',  '123456',    '56',        '123456'   ] ] )
    # Black Cell Analysis (found online)
    #test()

######################################################################################################################
    # Puzzles

def link_to_string(link):
    parts = [ ]
    link = link.strip()
    if len(link) > (81 + 81):
        black_offset = 81 + 81
    else:
        black_offset = 81
    for y in xrange(9):
        for x in xrange(9):
            offset = y * 9 + x
            d = link[offset]
            if link[black_offset + offset] == '1':
                # Black
                if d == '0':
                    parts.append('#')
                else:
                    parts.append(chr(ord(d) + 48))
            else:
                if d == '0':
                    parts.append('.')
                else:
                    parts.append(d)
        parts.append('\n')
    return ''.join(parts)

PUZZLES = {
    'easy1':       "f.3##..##\n41.3#.8.6\n..#..#...\n...b...7#\n#i..6..##\n#....#...\n..8#4.#6.\n..9.a2...\n##56#d2.#",
    'easy2':       "##..#c1.#\n.....#..#\n7.##3.e..\n..#5..7..\n.#..#.6i.\n4...65#..\n.2h..##..\nb3.#.....\n#43f#8.#a",
    'moderate1':   "#...7##.1\ne..7.#...\n.3a.....#\n42.#h...#\n....#.5..\n#4..##..6\n#7....#..\n...i...3#\n.9g#1...#",
    'moderate2':   "#a..9#..#\n......4.#\n...7e4.##\n#.5#2.#.6\n......6..\n5.#..i7.#\nc#..d....\n#....5...\n#..#..5#b",
    'tough1':      "##.6#..#c\n#..2#...#\n2.#.3.#..\n...5...7.\n##...1.f#\n.7.......\n.6#...i..\ne...a...#\n##..g..##",
    'tough2':      "#..##7..#\n#..#....b\n#.5.26...\n.....##..\n6.i1..#..\n..#h5....\n.......3#\n#..5.d..#\nc...a#..#",
    'diabolical1': "d9..cf..e\n....#....\n..#b..#..\n.........\n##3..4.a#\n........6\n..#..##.8\n1...i....\n#..##...#",
    'diabolical2': "#2..f...#\n....#..68\n..d...#..\n#........\n#a.2...##\n......1.i\n..#...#..\n7...#....\nb7..#..3#",
    'daily1866':   "#g.3#..#f\n....#h..#\n..a..#..7\n.3...4...\n##.6#..##\n...5.....\n.5.#..i..\n#..##..4.\n##..c..##",
    'daily1867':   "2.#....#i\n..#..#..7\n#...#f...\n...#...9#\n45#..8#.1\n#....#...\n.65#h4..#\n..7a2.#5.\n##....#..",
    'daily1868':   "#..f.4#..\n..9#..6.#\n.7c..#..#\n#1....i..\n....#....\n..#.....a\nd..#..#..\n#...5#...\n..#..#..g",
    'daily1869':   "#..a#..#.\ne..6i....\n6....#..b\n.7##..6..\n.3..6....\n.....##.8\nd..#.....\n....#9..#\n.#..c#..#",
    'daily1870':   "##..#..##\n.b..#..8d\n.9...1...\n#...5.#..\n..#...e..\n..#..4..i\n...6.9...\n#...f..#.\nc#8.#..#a",
    'daily1871':   "#7.e#3.##\n....#....\n..#9.fc2.\n...#4.#..\n#.6....9#\n.3#..#...\n..a#..#.4\n....i....\n##..##..g",
    'daily1872':   ".##.2#..c\n.......78\n#.3#..#..\n..a#.67#d\n.....8...\n##...##..\n..b..#..e\n.......4.\nf..i..##.",
    'daily1873':   "#1...#..e\n3......7#\n2..a#....\n...7..#h.\n##.....##\n.##.6..1.\n....##4..\ni........\n#..#...3f",
    'daily1874':   "e..#..#..\n...5.#a9.\n..#..#..g\n#7.i.....\n.4.7.....\n.....#3.#\n#..#.4#..\n..#c...6.\n.1#..#..#",
    'daily1875':   "c#2.##6.#\n.a...#.6.\n.9##..g.6\n7....3.1#\n#.7.#...e\n#....2...\n..#..i#.4\n...#...#.\nf.4##.8##"
}

if __name__ == "__main__":
    parser = ArgumentParser(
        formatter_class=RawDescriptionHelpFormatter,
        description=dedent('''\
            This application attempts to solve Str8ts puzzles available at:
                http://www.str8ts.com/

            All of the puzzles included in this application are to test the solving
            algorithms. Many of the puzzles included here were created by Andrew Stuart.
            Puzzles have also be included from the Weekly Extreme Str8ts discussions by
            Ulrich and Klaus:
                http://www.str8ts.com/weekly_str8ts.asp

            The solver implements many of the strategies described in "Str8ts Strategies"
            by SlowThinker. The document is available online at:
                http://www.slideshare.net/SlowThinker/str8ts-basic-and-advanced-strategies
                http://is.gd/slowthinker_str8ts_strategy

            The solver was implemented by @james_austin and is maintained at:
                https://github.com/jamesaustin/str8ts

            All contributions, improvements and optimisations are welcomed.
            '''),
        epilog=dedent('''\
            Coloured syntax highlighting:
              \033[107;30m x \033[0m digit is known
              \033[107;94m x \033[0m digit was given
              \033[40;97m x \033[0m black cell
              \033[100;30m x \033[0m unknown cell with possible digits
              \033[100;30m \033[43mx\033[100m \033[0m digit is a row compartment sure candidate
              \033[100;30m \033[46mx\033[100m \033[0m digit is a column compartment sure candidate
              \033[100;30m \033[42mx\033[100m \033[0m digit is both a row and column compartment sure candidate
              \033[100;31m x \033[0m digit was eliminated

            Verbose solutions use the following code, adapted from SlowThinker's scheme:
              N  - number was last candidate in the field
              s  - \033[4;1ms\033[0mingle candidate for number in compartment
              c  - \033[4;1mc\033[0mompartment range check
              d  - \033[4;1md\033[0migits stranded (unreachable / impossible)
              h  - \033[4;1mh\033[0migh / low range check across compartments
              L  - \033[4;1mL\033[0marge gap field
              p  - naked \033[4;1mp\033[0mair
              t  - naked \033[4;1mt\033[0mriple
              q  - naked \033[4;1mq\033[0muadruple
              p\033[2mh\033[0m - hidden \033[4;1mp\033[0mair
              t\033[2mh\033[0m - hidden \033[4;1mt\033[0mriple
              q\033[2mh\033[0m - hidden \033[4;1mq\033[0muadruple
              x\033[2mx\033[0m - \033[4;1mX\033[0m-wing (2 rows / 2 columns) on \033[4;1mx\033[0m
              w\033[2mx\033[0m - S\033[4;1mw\033[0mordfish (3 rows / 3 columns) on \033[4;1mx\033[0m
              j\033[2mx\033[0m - \033[4;1mJ\033[0mellyfish (4 rows / 4 columns) on \033[4;1mx\033[0m
              S\033[2mx\033[0m - \033[4;1mS\033[0metti's rule on \033[4;1mx\033[0m
              u  - \033[4;1mu\033[0mnique rectangle
              y  - \033[4;1mY\033[0m-Wing or X\033[4;1mY\033[0m-chains

            |<-- This application is best run in a terminal with at least 93 columns. ----------------->|
            '''))
    parser.add_argument('puzzle', type=str, nargs='*')
    parser.add_argument('-v', '--verbose', action='store_true', help='show final solver results')
    parser.add_argument('-d', '--debug', action='store_true', help='show all solver iterations')
    parser.add_argument('-s', '--sure', action='store_true', help='include sure candidates in debug')
    parser.add_argument('-l', '--list', action='store_true', help='list known puzzles and exit')
    parser.add_argument('-i', '--include', help='load puzzles from external file')
    parser.add_argument('-c', '--chain-length', type=int, default=4,
                        help='maximum length of cell to search for contradictions')
    parser.add_argument('--no-tests', dest='tests', action='store_false', help='disable built in technique tests')
    parser.add_argument('--no-counts', dest='counts', action='store_false', help='disable technique counts')
    parser.add_argument('--no-totals', dest='totals', action='store_false', help='disable solver success counts')
    parser.add_argument('--tidy', action='store_true', help='tidy the included puzzles and exit')
    args = parser.parse_args()

    if args.tidy and args.include:
        with open(args.include) as f:
            for line in f:
                line = line.strip()
                if line[0] == '#':
                    print(line)
                else:
                    parts = line.split(':')
                    name = parts[0].strip()
                    puzzle = parts[1].strip()
                    if len(puzzle) > (81 + 81):
                        puzzle = '{}{}'.format(puzzle[:81], puzzle[-81:])
                    print('{}:{}'.format(name, puzzle))
        exit()

    if args.include:
        with open(args.include) as f:
            for line in f:
                if line[0] == '#':
                    continue
                parts = line.split(':')
                PUZZLES[parts[0]] = link_to_string(parts[1])

    if not args.puzzle:
        puzzles = sorted(PUZZLES.keys())
    else:
        puzzles = [p for puzzle in args.puzzle for p in PUZZLES.keys() if fnmatch(p, puzzle)]

    if args.list:
        for p in puzzles:
            if args.verbose:
                _comment('{}'.format(p))
                print(Board(PUZZLES[p]))
            else:
                print(p)
        exit()

    if args.tests:
        _comment('Testing techniques')
        tests()

    def _log_exception(name, e, b):
        _critical('Invalid board for "{0}", {1[0]}{1[1]} {2} is {1[2]}'.format(
            name, e, ''.join(b[e[0], e[1]].digits)))
        print(b._to_string())

    counts = Counter()
    hits = Counter()
    success, failed = 0, 0
    if puzzles:
        _comment('Puzzle       [Iter] [Techniques] [Digits #  ]')
        for name in puzzles:
            b = Board(PUZZLES[name], args.chain_length)
            try:
                if b.solve(name, verbose=args.verbose, debug=args.debug, sure=args.sure):
                    success += 1
                else:
                    failed += 1
                for rule, count in b.counts.iteritems():
                    counts[rule] += count
                for rule, hit in b.hits.iteritems():
                    hits[rule] += hit
            except Board.InvalidSolution as e:
                _log_exception(name, e, b)
                b = Board(PUZZLES[name])
                try:
                    b.solve(name, debug=True)
                except Board.InvalidSolution as f:
                    _log_exception(name, f, b)
                    exit()
    if args.counts:
        counts_total = sum(counts.values())
        hits_total = sum(hits.values())
        rules = [r.__name__ for r in Board.steps]
        _comment('Technique                      [Ord] [Hit %  Hit #] [Digit %  Digit #]')
        for rule, hit in sorted(hits.iteritems(), reverse=True, key=lambda k_v: k_v[1]):
            _hit(' {:<30} [#{:2}] [{:>5.1%} {:>6}] [{:>5.1%} {:>10}]'.format(rule, rules.index(rule),
                float(hit) / hits_total, hit, float(counts[rule]) / counts_total, counts[rule]))
        for rule_fn in Board.steps:
            rule = rule_fn.__name__
            if rule not in hits:
                _miss('{:<30} [#{:2}]'.format(rule, rules.index(rule)))
    if args.totals:
        _comment('Total # Puzzles')
        _pass('{} boards'.format(success))
        _fail('{} boards'.format(failed))
