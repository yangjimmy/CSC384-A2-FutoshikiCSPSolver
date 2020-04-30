#Look for #IMPLEMENT tags in this file. These tags indicate what has
#to be implemented to complete problem solution.  

'''This file will contain different constraint propagators to be used within 
   bt_search.

   propagator == a function with the following template
      propagator(a2 csp, newly_instantiated_variable=None)
           ==> returns (True/False, [(Variable, Value), (Variable, Value) ...]

      a2 csp is a CSP object---the propagator can use this to get access
      to the variables and constraints of the problem. The assigned variables
      can be accessed via methods, the values assigned can also be accessed.

      newly_instantiated_variable is an optional argument.
      if newly_instantiated_variable is not None:
          then newly_instantiated_variable is the most
           recently assigned variable of the a1 search.
      else:
          progator is called before any assignments are made
          in which case it must decide what processing to do
           prior to any variables being assigned. SEE BELOW

       The propagator returns True/False and a list of (Variable, Value) pairs.
       Return is False if a deadend has been detected by the propagator.
       in this case bt_search will backtrack
       return is true if we can continue.

      The list of variable values pairs are all of the values
      the propagator pruned (using the variable's prune_value method). 
      bt_search NEEDS to know this in order to correctly restore these 
      values when it undoes a variable assignment.

      NOTE propagator SHOULD NOT prune a value that has already been 
      pruned! Nor should it prune a value twice

      PROPAGATOR called with newly_instantiated_variable = None
      PROCESSING REQUIRED:
        for plain backtracking (where we only check fully instantiated 
        constraints) 
        we do nothing...return true, []

        for forward checking (where we only check constraints with one
        remaining variable)
        we look for unary constraints of the a2 csp (constraints whose scope
        contains only one variable) and we forward_check these constraints.

        for gac we establish initial GAC by initializing the GAC queue
        with all constraints of the a2 csp


      PROPAGATOR called with newly_instantiated_variable = a variable V
      PROCESSING REQUIRED:
         for plain backtracking we check all constraints with V (see a2 csp method
         get_cons_with_var) that are fully assigned.

         for forward checking we forward check all constraints with V
         that have one unassigned variable left

         for gac we initialize the GAC queue with all constraints containing V.
		 
		 
var_ordering == a function with the following template
    var_ordering(a2 csp)
        ==> returns Variable 

    a2 csp is a CSP object---the heuristic can use this to get access to the
    variables and constraints of the problem. The assigned variables can be
    accessed via methods, the values assigned can also be accessed.

    var_ordering returns the next Variable to be assigned, as per the definition
    of the heuristic it implements.
   '''

def prop_BT(csp, newVar=None):
    '''Do plain backtracking propagation. That is, do no 
    propagation at all. Just check fully instantiated constraints'''
    
    if not newVar:
        return True, []
    for c in csp.get_cons_with_var(newVar):
        if c.get_n_unasgn() == 0:
            vals = []
            vars = c.get_scope()
            for var in vars:
                vals.append(var.get_assigned_value())
            if not c.check(vals):
                return False, []
    return True, []

def prop_FC(csp, newVar=None):
    '''Do forward checking. That is check constraints with 
       only one uninstantiated variable. Remember to keep 
       track of all pruned variable,value pairs and return '''
    if newVar is not None:
        cons_list = csp.get_cons_with_var(newVar)
    else:
        cons_list = csp.get_all_cons()
        # do not choose a variable, instead look for unary constraints

    pruned_vals = []
    for c in cons_list:
        if c.get_n_unasgn() == 1:
            x = c.get_unasgn_vars()[0]
            x_domain = []
            for idx in range(len(x.curdom)):
                if x.curdom[idx]:  # true, unpruned
                    x_domain.append(x.dom[idx])
            # check
            if x.cur_domain() == []:
                return False, []
            for xVal in x_domain:
                x.assign(xVal)
                scope = c.get_scope()
                vals = []
                for var in scope:
                    vals.append(var.get_assigned_value())
                x.unassign()
                if not c.check(vals):
                    # prune the value from x
                    x.prune_value(xVal)
                    pruned_vals.append((x,xVal))
                if x.cur_domain() == []:
                    # need to return pruned values to un-prune everything
                    return False, pruned_vals
    return True, pruned_vals

def prop_GAC(csp, newVar=None):
    '''Do GAC propagation. If newVar is None we do initial GAC enforce 
       processing all constraints. Otherwise we do GAC enforce with
       constraints containing newVar on GAC Queue'''
    if newVar is None:
        constraint_queue = csp.get_all_cons()
    else:
        constraint_queue = csp.get_cons_with_var(newVar)
    # begin processing
    pruned_all = []
    while constraint_queue != []:
        c, constraint_queue = dequeue(constraint_queue)
        vars_all = c.get_scope()
        for var in vars_all:
            # check domain to see if there is support, if not then add to prune
            # and add constraints that involve the variable to constraints queue
            if var.is_assigned():
                continue
            pruned_count = 0
            for var_idx in range(len(var.curdom)):
                if var.curdom[var_idx]:  # in current domain
                    val = var.dom[var_idx]
                    if (var, val) not in pruned_all:
                        if not c.has_support(var, val):
                            pruned_count += 1
                            var.prune_value(val)
                            pruned_all.append((var, val))
                            cons_with_var = csp.get_cons_with_var(var)
                            # add constraints that involve the variable to constraints queue
                            for cv in cons_with_var:
                                if cv not in constraint_queue or cv.name != c.name:
                                    constraint_queue = enqueue(constraint_queue, cv)
                else:
                    # already pruned
                    pruned_count += 1
            if pruned_count == var.domain_size():
                # number of values pruned from variable is equal to total domain - dead state
                return False, pruned_all
    return True, pruned_all

def enqueue(lst,val):
    '''
    enqueue from the back
    :param lst: list, type list
    :param val: value
    :return: list
    '''
    lst.append(val)
    return lst

def dequeue(lst):
    '''
    dequeue from the front
    :param lst:
    :param val:
    :return:
    '''
    rval = lst.pop(0)
    return rval, lst


def ord_mrv(csp):
    ''' return variable according to the Minimum Remaining Values heuristic '''
    curr_min = float('inf')  # minimum domain length found so far
    curr_var = None
    for var in csp.get_all_unasgn_vars():
        if var.cur_domain_size() < curr_min:
            curr_min = var.cur_domain_size()
            curr_var = var
    return curr_var
