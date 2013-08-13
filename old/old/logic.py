################################################################################
#
# logic.py
#
# description: Strict and non-strict logical combinators for semantic values
#
#
# Authors:
# Jeremy Avigad
# Cody Roux
#
#
################################################################################

################################################################################
#
# Strict operators
#
################################################################################



def strict_true():
    """Strict true boolean
    """
    return True

def strict_false():
    """Strict false boolean
    """
    return False

def strict_neg(a):
    """Strict negation
    
    Arguments:
    - `a`: a boolean
    """
    return not a


def strict_conj(a, b):
    """Strict conjunction
    
    Arguments:
    - `a`: a boolean
    - `b`: a boolean
    """
    return a & b

def strict_disj(a, b):
    """Strict disjunction
    
    Arguments:
    - `a`: a boolean
    - `b`: a boolean
    """
    return a | b

def strict_and(* a):
    """Strict varyadic and
    
    Arguments:
    - `* a`: a list of booleans
    """
    return reduce(lambda x, y: x & y, a, True)

def strict_or(* a):
    """Strict varyadic and
    
    Arguments:
    - `* a`: a list of booleans
    """
    return reduce(lambda x, y: x | y, a, True)

def strict_impl(a, b):
    """Strict implication
    
    Arguments:
    - `a`: a boolean
    - `b`: a boolean
    """
    return (not a) or b


def strict_forall(l, f):
    """Takes an iterable of elements, and returns (True, None)
    if f applied to each element returns True. Otherwise
    it returns (False, e) where e is the first element for which
    f returns False.
    
    Arguments:
    - `l`: an iterable of elements
    - `f`: a function that applies to these elements
    """
    for e in l:
        if f(e) == False:
            return (False, e)
        elif f(e) == True:
            pass
        else:
            raise TypeError("Expected a Boolean")
    return (True, None)

def strict_exists(l, f):
    """Takes an iterable of elements, and returns (False, None)
    if f applied to each element returns False. Otherwise
    it returns (True, e) where e is the first element for which
    f returns True.
    
    Arguments:
    - `l`: an iterable of elements
    - `f`: a function that applies to these elements
    """
    for e in l:
        if f(e) == True:
            return (True, e)
        elif f(e) == False:
            pass
        else:
            raise TypeError("Expected a Boolean")
    return (False, None)

def strict_eq(a, b):
    """Strict equality of objects.
    
    Arguments:
    - `a`: a python object
    - `b`: a python object
    """
    return a == b

def strict_neq(a, b):
    """Strict disequality of objects.
    
    Arguments:
    - `a`: a python object
    - `b`: a python object
    """
    return a != b


################################################################################
#
# Non-strict operators
#
################################################################################

def non_strict_true():
    """Non-strict true boolean
    """
    return True

def non_strict_false():
    """Non-strict false boolean
    """
    return False

def non_strict_neg(a):
    """Non-strict negation
    
    Arguments:
    - `a`: a boolean
    """
    if a == None:
        return None
    else:
        return not a

def non_strict_conj(a, b):
    """Non-strict conjunction
    
    Arguments:
    - `a`: a boolean
    - `b`: a boolean
    """
    if a == False:
        return False
    elif b == False:
        return False
    elif a == True and b == True:
        return True
    else:
        return None

def non_strict_disj(a, b):
    """Non-strict disjunction
    
    Arguments:
    - `a`: a boolean
    - `b`: a boolean
    """
    if a == True:
        return True
    elif b == True:
        return True
    elif a == False and b == False:
        return False
    else:
        return None

def non_strict_and(* a):
    """Non-strict varyadic and
    
    Arguments:
    - `* a`: a list of booleans
    """
    return non_strict_forall(a, lambda b: b)[0]
    
def non_strict_or(* a):
    """Non-strict varyadic and
    
    Arguments:
    - `* a`: a list of booleans
    """
    return non_strict_exists(a, lambda b: b)[0]

def non_strict_impl(a, b):
    """Non-strict implication
    
    Arguments:
    - `a`: a boolean
    - `b`: a boolean
    """
    if a == False:
        return True
    elif a == True:
        return b
    elif b == True:
        return True
    else:
        return None

def non_strict_forall(l, f):
    """Returns a pair (b, e) where b is the truth value
    of forall l, f(l) and e is a counter-example or None.
    
    Arguments:
    - `l`: an iterable of elements
    - `f`: a function that applies to these elements
    """
    result = True
    for e in l:
        if f(e) == False:
            return (False, e)
        elif f(e) == True:
            pass
        else:
            result = None
    return (result, None)

def non_strict_exists(l, f):
    """Returns a pair (b, e) where b is the non-struct
    truth value of exists l, f(l) and e is
    a witness or None.

    Arguments:
    - `l`: an iterable of elements
    - `f`: a function that applies to these elements
    """
    result = False
    for e in l:
        if f(e) == True:
            return (True, e)
        elif f(e) == False:
            pass
        else:
            result = None
    return (result, None)

def non_strict_eq(a, b):
    """Equality between non-strict values
    
    Arguments:
    - `a`: a value or None
    - `b`: a value of a type comparable to a or None
    """
    if a == None or b == None:
        return None
    else:
        return a == b
    
def non_strict_neq(a, b):
    """Disequality between non-strict values
    
    Arguments:
    - `a`: a value or None
    - `b`: a value of a type comparable to a or None
    """
    if a == None or b == None:
        return None
    else:
        return a != b
    

#####################################################################
#
# Combinators for partial functions
#
#####################################################################

def partial(f, args):
    """
    
    Arguments:
    - `f`: a function of a value tuple to values
    - `args`: a tuple of arguments for f, may contain None
    elements
    """
    if None in args:
        return None
    else:
        return f(*args)

def bottom_lift(f, args):
    """Calls f on the arguments, returns None if there is
    an error of any sort. USE WITH CAUTION
    
    Arguments:
    - `f`: a function
    - `args`: a tuple of arguments
    """
    try:
        return f(*args)
    except Exception:
        return None


#####################################################################
#
#Some tests
#
#####################################################################

if __name__ == '__main__':


    l = [1, 2, 3, 4, 5, 6]
    ll = [2, 4, 6, 8, 10]
    l3 = [True, True, True]
    l4 = [True, None, False]
    l5 = [True, None, True]
    
    def f(x):
        if x%2 == 0:
            return True
        else:
            return None

    print non_strict_exists(l, f)

    print non_strict_forall(l, f)

    print non_strict_forall(ll, f)
    print

    print non_strict_conj(True, False)
    print non_strict_conj(True, True)
    print non_strict_conj(False, None)
    print non_strict_conj(True, None)
    print

    print non_strict_disj(True, False)
    print non_strict_disj(True, True)
    print non_strict_disj(False, None)
    print non_strict_disj(True, None)
    print

    print non_strict_or(*l4)
    print non_strict_or(*l5)
    print non_strict_and(*l3)
    print non_strict_and(*l4)
    print non_strict_and(*l5)
