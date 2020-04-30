# Look for #IMPLEMENT tags in this file.
'''
All models need to return a CSP object, and a list of lists of Variable objects 
representing the board. The returned list of lists is used to access the 
solution. 

For example, after these three lines of code

    a2 csp, var_array = futoshiki_csp_model_1(board)
    solver = BT(a2 csp)
    solver.bt_search(prop_FC, var_ord)

var_array[0][0].get_assigned_value() should be the correct value in the top left
cell of the Futoshiki puzzle.

1. futoshiki_csp_model_1 (worth 20/100 marks)
    - A model of a Futoshiki grid built using only 
      binary not-equal constraints for both the row and column constraints.

2. futoshiki_csp_model_2 (worth 20/100 marks)
    - A model of a Futoshiki grid built using only n-ary 
      all-different constraints for both the row and column constraints. 

'''

from cspbase import *
import itertools


def futoshiki_csp_model_1(futo_grid):
    """
    :type futo_grid: list
    :param futo_grid:
    :return: csp, variables array
    """
    board_size = (len(futo_grid[0]) + 1) // 2
    # step 1. initialize with set of variables
    # length of futo_grid should equal board_size
    assert (board_size == len(futo_grid))  # for debugging
    cons_unary = [] # unary constraints for variables with variables already set
    vars_all_2d = []
    vars_all_1d = []
    for row_idx in range(len(futo_grid)):
        row = futo_grid[row_idx]
        vars_row = []
        for col_idx in range(board_size):
            item_idx = col_idx * 2
            item = row[item_idx]
            var_name = str(row_idx) + ' , ' + str(item_idx//2)  # unique naming scheme named according to position, (row, col)
            domain = list(range(1, board_size + 1))
            new_var = Variable(var_name, domain)
            if item!=0:
                # get a constraint
                cons_name = var_name+' unary'
                cons_scope = [new_var]
                new_cons = Constraint(cons_name,cons_scope)
                new_cons.add_satisfying_tuples([(item,)])
                cons_unary.append(new_cons)
            vars_row.append(new_var)
        vars_all_2d.append(vars_row)
        vars_all_1d.extend(vars_row)
    new_csp = CSP("Futoshiki Model 1", vars_all_1d)
    for constraint in cons_unary:
        new_csp.add_constraint(constraint)

    # step 2. find inequality constraints on row
    for row_idx in range(len(futo_grid)):
        for col_idx in range(board_size - 1):
            item_idx = col_idx * 2 + 1
            item = futo_grid[row_idx][item_idx]
            if item != '.':
                var1 = vars_all_2d[row_idx][col_idx]
                var2 = vars_all_2d[row_idx][col_idx + 1]
                scope = [var1, var2]
                name = var1.name + item + var2.name
                cons = Constraint(name, scope)
                tuple_list = []
                if item == '>':
                    for i in range(1, board_size):
                        for j in range(i+1, board_size+1):
                            tuple_list.append((j, i))
                    cons.add_satisfying_tuples(tuple_list)
                    new_csp.add_constraint(cons)
                elif item == '<':
                    for i in range(1, board_size):
                        for j in range(i+1, board_size+1):
                            tuple_list.append((i, j))
                    cons.add_satisfying_tuples(tuple_list)
                    new_csp.add_constraint(cons)
                else:
                    raise ValueError("incorrect board character {}".format(item))

    # possible values along row, column
    pos_vals = list(range(1, board_size + 1))
    # not equal, row
    for row_idx in range(board_size):
        # all pairs of variables in a row
        for col_idx1 in range(board_size):
            var1 = vars_all_2d[row_idx][col_idx1]
            for col_idx2 in range(board_size):
                if col_idx1 != col_idx2:
                    var2 = vars_all_2d[row_idx][col_idx2]
                    scope = [var1, var2]
                    name = var1.name + " not equal " + var2.name
                    cons = Constraint(name, scope)
                    tuple_list = list(itertools.permutations(pos_vals, 2))
                    cons.add_satisfying_tuples(tuple_list)
                    new_csp.add_constraint(cons)

    # not equal, column
    for col_idx in range(board_size):
        # all possible pairs in a column
        for row_idx1 in range(board_size):
            var1 = vars_all_2d[row_idx1][col_idx]
            for row_idx2 in range(board_size):
                if row_idx1 != row_idx2:
                    var2 = vars_all_2d[row_idx2][col_idx]
                    scope = [var1, var2]
                    name = var1.name + " not equal " + var2.name
                    cons = Constraint(name, scope)
                    tuple_list = list(itertools.permutations(pos_vals, 2))
                    cons.add_satisfying_tuples(tuple_list)
                    new_csp.add_constraint(cons)

    return new_csp, vars_all_2d


def futoshiki_csp_model_2(futo_grid):
    """

    :param futo_grid: fukoshiki grid, 2d array format specified in handout
    :return: csp, variables array
    """
    board_size = (len(futo_grid[0]) + 1) // 2
    # step 1. initialize with set of variables
    # length of futo_grid should equal board_size
    assert (board_size == len(futo_grid))  # for debugging
    cons_unary = []
    vars_all_2d = []
    vars_all_1d = []
    for row_idx in range(len(futo_grid)):
        row = futo_grid[row_idx]
        vars_row = []
        for col_idx in range(board_size):
            item_idx = col_idx * 2
            item = row[item_idx]
            var_name = str(row_idx) + ' , ' + str(item_idx//2)  # unique naming scheme named according to position, (row, col)
            domain = list(range(1, board_size + 1))
            new_var = Variable(var_name, domain)
            if item != 0:
                #domain = [item]
                cons_name = var_name + ' unary'
                cons_scope = [new_var]
                new_cons = Constraint(cons_name, cons_scope)
                new_cons.add_satisfying_tuples([(item,)])
                cons_unary.append(new_cons)
            vars_row.append(new_var)
        vars_all_2d.append(vars_row)
        vars_all_1d.extend(vars_row)
    new_csp = CSP("Futoshiki Model 2", vars_all_1d)
    for constraint in cons_unary:
        new_csp.add_constraint(constraint)

    # step 2. find inequality constraints on row
    for row_idx in range(len(futo_grid)):
        for col_idx in range(board_size - 1):
            item_idx = col_idx * 2 + 1
            item = futo_grid[row_idx][item_idx]
            if item != '.':
                var1 = vars_all_2d[row_idx][col_idx]
                var2 = vars_all_2d[row_idx][col_idx + 1]
                scope = [var1, var2]
                name = var1.name + item + var2.name
                cons = Constraint(name, scope)
                tuple_list = []
                if item == '>':
                    for i in range(1, board_size):
                        for j in range(i + 1, board_size + 1):
                            tuple_list.append((j, i))
                    cons.add_satisfying_tuples(tuple_list)
                    new_csp.add_constraint(cons)
                elif item == '<':
                    for i in range(1, board_size):
                        for j in range(i + 1, board_size + 1):
                            tuple_list.append((i, j))
                    cons.add_satisfying_tuples(tuple_list)
                    new_csp.add_constraint(cons)
                else:
                    raise ValueError("incorrect board character {}".format(item))

    # not equal, row
    for row_idx in range(board_size):
        # all pairs of variables in a row
        scope = []
        for col_idx in range(board_size):
            scope.append(vars_all_2d[row_idx][col_idx])
        name = "all-diff row " + str(row_idx)
        cons = Constraint(name, scope)
        pos_vals = list(range(1, board_size + 1))
        perm = list(itertools.permutations(pos_vals))
        cons.add_satisfying_tuples(perm)
        new_csp.add_constraint(cons)
        print("Done")

    # not equal, column
    for col_idx in range(board_size):
        scope = []
        for row_idx in range(board_size):
            scope.append(vars_all_2d[row_idx][col_idx])
        name = "all-diff column " + str(col_idx)
        cons = Constraint(name, scope)
        pos_vals = list(range(1, board_size + 1))
        perm = list(itertools.permutations(pos_vals))
        cons.add_satisfying_tuples(perm)
        new_csp.add_constraint(cons)
        print("Done")

    return new_csp, vars_all_2d
