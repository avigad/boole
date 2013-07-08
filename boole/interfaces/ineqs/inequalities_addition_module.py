from inequalities_classes import *
from inequalities_heuristic import *

###############################################################################
#
# ADDITIVE ELIMINATION
#
###############################################################################

# The additive procedure works with inequalities like t > 0, where
# t is an Add_term
class Zero_comparison:

    def __init__(self, term, comp):
        self.term = term
        self.comp = comp

    def __str__(self):
        return str(self.term) + ' ' + comp_str[self.comp] + ' 0'

    def __repr__(self):
        return self.__str__()
    
    def __eq__(self,other):
        if not isinstance(other,Zero_comparison):
            return False
        return self.comp == other.comp and self.term == other.term
        
#
# The next routine takes additive terms t1 and t2, and another term
#   v (usually a variable), which appears t1.
#
# It returns the result of solving for v in the equation t1 = 0, and
#   substituting the result in t2.
#
def add_subst(t1, t2, v):
    addpairs2 = list(t2.addpairs)
    # if v doesn't appear in t2, just return t2
    i2 = next((i for i in range(len(addpairs2)) if addpairs2[i].term == v), None)
    if i2 is None:
        return t2
    a2 = addpairs2[i2].coeff
    addpairs2.pop(i2)
    
    addpairs1 = list(t1.addpairs)
    i1 = next((i for i in range(len(addpairs1)) if addpairs1[i].term == v))
    a1 = addpairs1[i1].coeff
    addpairs1.pop(i1)
    retval = Add_term(addpairs2) + Add_term(addpairs1) * (-Fraction(a2, a1))
    
    #retval.addpairs.sort() #If we are filtering for repeats, sorting the terms is necessary. Otherwise, it does nothing.
    return retval

def add_elim(equations, zero_comparisons, v):
    #print 'running add_elim to eliminate',v,'. eqns len=',len(equations),'comps len=',len(zero_comparisons)

    def occurs_in(v,t):
        return v in (a.term for a in t.addpairs)
    
    #Find the shortest equation that contains v, if it exists. solve it for v and substitute into others
    shortest_eqn = None
    for e in equations:
        if occurs_in(v,e) and ((not shortest_eqn) or len(e.addpairs) < len(shortest_eqn.addpairs)):
            shortest_eqn = e
    
    if shortest_eqn:
        e = shortest_eqn
        new_equations = [add_subst(e, e2, v) for e2 in equations if e != e2]
        new_comparisons = [Zero_comparison(add_subst(e,c.term,v),c.comp) for c in zero_comparisons]
        
        #Filters new_equations and new_comparisons for repeats. Not currently used.
        #new_equations = []
        #for e2 in equations:
        #    if e!=e2:
        #        ne = add_subst(e,e2,v)
        #        #if ne not in new_equations:
        #        new_equations.append(ne)
        #            
        #new_comparisons = []
        #for c in zero_comparisons:
        #    nc = Zero_comparison(add_subst(e,c.term,v),c.comp)
        #    #if str(nc) not in [str(t) for t in new_comparisons]:
        #        new_comparisons.append(nc)
            
        return new_equations, new_comparisons
    
    #Otherwise, there is no equation that contains v.
    
    pos_comparisons = []  # v occurs positively
    neg_comparisons = []  # v occurs negatively
    new_comparisons = []
    
    #If we are filtering for repeats, it is much more efficient to store comparisons in a hashmap.
    #new_comparisons = {}
    #def add_to_new_comps(zerocomp):
    #    try:
    #        s = new_comparisons[str(zerocomp)]
    #    except KeyError:
    #        new_comparisons[str(zerocomp)]=zerocomp
    
    for c in zero_comparisons:
        try:
            a = next((a for a in c.term.addpairs if a.term == v))
            if a.coeff > 0:
                pos_comparisons.append(c)
            else:
                neg_comparisons.append(c)
        except StopIteration:  # v does not occur at all
            #if c not in new_comparisons:
            new_comparisons.append(c)
            #add_to_new_comps(c)
                
    #if len(zero_comparisons)>100: print 'length of pos_comps:',len(pos_comparisons),'length of neg_comps:',len(neg_comparisons),'length of new_comps:',len(new_comparisons.keys())
    for c1 in pos_comparisons:
        for c2 in neg_comparisons:
            #print c1,c2
            if c1.comp == GE and c2.comp == GE:
                new_comp = GE
            else:
                new_comp = GT
            new_zc = Zero_comparison(add_subst(c1.term,c2.term,v),new_comp)
            #if new_zc not in new_comparisons:
            new_comparisons.append(new_zc)
            #add_to_new_comps(new_zc)
                    
    return equations,new_comparisons# [new_comparisons[c] for c in new_comparisons.keys()]

def learn_add_comparisons(H):

    def learn_add_comparison(c):
        length = len(c.term.addpairs)
        if length == 0:
            if c.comp == GT:
                H.raise_contradiction(ADD)
        elif length == 1:
            a = c.term.addpairs[0]
            i = a.term.index
            if a.coeff > 0:
                comp = c.comp
            else:
                comp = comp_reverse(c.comp)
            H.learn_zero_comparison(i, comp, ADD)
        elif length == 2:
            a0 = c.term.addpairs[0]
            i0 = a0.term.index
            c0 = a0.coeff
            a1 = c.term.addpairs[1]
            i1 = a1.term.index
            c1 = a1.coeff
            coeff = -Fraction(c1, c0)
            if c0 < 0:
                comp = comp_reverse(c.comp)
            else:
                comp = c.comp
            H.learn_term_comparison(i0, i1, comp, coeff, ADD)

    if H.verbose:
        print "Learning additive facts..."
        print

    # make additive equations
    add_eqs = [H.name_defs[i] + Add_term([(-1, IVar(i))])
        for i in range(H.num_terms) if isinstance(H.name_defs[i], Add_term)]
    
    add_eqs.extend([c for c in H.zero_equations if isinstance(c,Add_term)])
    
    if H.verbose:
        print "Additive equations:"
        for t in add_eqs:
            print t, "= 0"
        print
    
    #Try to mine sign data from additive definitions.    
    for j in (i for i in range(H.num_terms) if (isinstance(H.name_defs[i],Add_term) and H.sign(i)==0)):
        addpairs = H.name_defs[j].addpairs
        sign = addpairs[0].coeff * H.weak_sign(addpairs[0].term.index)
        if sign != 0 and all(addpairs[i].coeff * H.weak_sign(addpairs[i].term.index) == sign for i in range(len(addpairs))):
            if any(H.sign(addpairs[i].term.index)!=0 for i in range(len(addpairs))):
                H.learn_zero_comparison(j,(GT if sign>0 else LT),ADD)
            else:
                H.learn_zero_comparison(j,(GE if sign>0 else LE),ADD)
                

    # make additive comparisons
    add_comps = []
    for i in H.zero_comparisons.keys():
        if H.zero_comparisons[i].provenance != ADD:
            # otherise, additive routine can already see this fact
            comp = H.zero_comparisons[i].comp
            if comp in [GT, GE]:
                add_comps.append(Zero_comparison(Add_term([(1, IVar(i))]), 
                                                 comp))
            else:
                add_comps.append(Zero_comparison(Add_term([(-1, IVar(i))]), 
                                                 comp_reverse(comp)))
    for (i, j) in H.term_comparisons.keys():
        for c in H.term_comparisons[i,j]:
            if c.provenance != ADD:
                if c.comp in [GT, GE]:
                    add_comps.append(Zero_comparison(
                        Add_term([(1, IVar(i)), (-1*c.coeff, IVar(j))]), c.comp))
                else:
                    add_comps.append(Zero_comparison(
                        Add_term([(-1, IVar(i)), (c.coeff, IVar(j))]), 
                                 comp_reverse(c.comp)))

    if H.verbose:
        print "Additive comparisons:"
        for c in add_comps:
            print c
        print
    
    #Checks to see if it will be helpful to put c into add_comps    
    def is_useful_comp(c,add_comps):
        sign = c.term.addpairs[0].coeff*H.sign(c.term.addpairs[0].term.index)
        bool = True
        for m in c.term.addpairs:
            if m.coeff*H.sign(m.term.index)*sign<=0:
                bool = False
                break
        if bool:
            # all added pieces have the same sign.
            #print 'c is useless!',c
            if sign<0 and c.comp in [GE,GT]: H.raise_contradiction(MUL)
            return False
            #ij_add_comps.remove(c)
            
        if len(c.term.addpairs)==1:
            i = c.term.addpairs[0].term.index
            comps = [co for co in add_comps if len(co.term.addpairs)==1 and co.term.addpairs[0].term.index==i]
            if comps:
                return False
            return True
        
        if len(c.term.addpairs)==2:
            i,j = c.term.addpairs[0].term.index,c.term.addpairs[1].term.index
            comps = [co for co in add_comps if len(co.term.addpairs)==2 and co.comp==c.comp and co.term.addpairs[0].term.index==i and co.term.addpairs[1].term.index==j]
            new_comp_data = Comparison_data(c.comp,-c.term.addpairs[1].coeff)
            comp_data = [Comparison_data(co.comp,-co.term.addpairs[1].coeff) for co in comps]
            #if H.sign(j)>0 and 
            

    for i in range(H.num_terms):
        # get all comparisons with i
        i_add_eqs = add_eqs
        i_add_comps = add_comps
        for j in range(i+1, H.num_terms):
            # get all comparisons with i and j
            ij_add_eqs = i_add_eqs
            ij_add_comps = i_add_comps
            for k in range(j+1, H.num_terms):
                #print 'reducing down to',IVar(i),'and',IVar(j),'. eliminating',IVar(k),'length of comps is currently',len(ij_add_comps),'(length of eqns is',len(ij_add_eqs),')'
                #if len(ij_add_comps)>1000:
                #    print ij_add_comps

                ij_add_eqs, ij_add_comps = (
                    add_elim(ij_add_eqs, ij_add_comps, IVar(k)))
                
            # add any new information
            #print 'i,j=',i,j,'. length of ij_add_comps is',len(ij_add_comps)
            for c in ij_add_comps:
                learn_add_comparison(c)
            # eliminate j
            i_add_eqs, i_add_comps = add_elim(i_add_eqs, i_add_comps, IVar(j))
        add_eqs, add_comps = add_elim(add_eqs, add_comps, IVar(i))
    print

def test_add_subst():

    x = Var('x')
    y = Var('y')
    z = Var('z')
    w = Var("w")
    t1 = Add_term([(3, x), (4, y), (-2, z)])
    t2 = Add_term([(-2, x), (-2, y), (5, z)])

    print "t1 = ", t1
    print "t2 = ", t2
    print "t1 + t2 = ", t1 + t2
    print "t1 * 3 + t2 * -1 = ", t1 * 3 + t2 * -1
    print "t1 + x =", t1 + x
    print "t1 + w =", t1 + w
    print "eliminate x:", add_subst(t1, t2, x)
    print "eliminate y:", add_subst(t1, t2, y)
    print "eliminate z:", add_subst(t1, t2, z)