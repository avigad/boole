from inequalities_classes import *

###########################################
#
#    COMPARISON DATA CLASSES
#
###########################################



#Comparison between one term a_i and 0
#a_i comp 0
class Zero_comparison_data:

    def __init__(self, comp, provenance=None):
        self.comp = comp
        self.provenance = provenance

    def to_string(self, term):
        return str(term) + ' ' + comp_str[self.comp] +  ' 0'

#comparison between two terms, a_i and a_j
#a_i comp coeff * a_j
class Comparison_data:

    def __init__(self, comp, coeff = 1, provenance = None):
        self.comp = comp
        self.coeff = coeff
        self.provenance = provenance

    def to_string(self, term1, term2):
        if self.coeff == 1:
            return str(term1) + ' ' + comp_str[self.comp] +  ' ' + str(term2)
        else:
            return (str(term1) + ' ' + comp_str[self.comp] +  ' ' + 
                    str(self.coeff) + '*' + str(term2))
                    
    def __str__(self):
        return 'comparison: '+comp_str[self.comp]+' '+str(self.coeff)
        
    def __repr__(self):
        return self.__str__()
    
    #used to figure out strength of inequalities
        
    def ge(self,other):
        if (self.comp in [LT,LE] and other.comp in [GT,GE]) or (self.comp in [GT,GE] and other.comp in [LT,LE]):
            return True
        return self.coeff>other.coeff or (self.coeff == other.coeff and self.comp in [LT,GT] and other.comp in [LE,GE])
        
    def le(self,other):
        if (self.comp in [LT,LE] and other.comp in [GT,GE]) or (self.comp in [GT,GE] and other.comp in [LT,LE]):
            return True
        return self.coeff<other.coeff or (self.coeff == other.coeff and self.comp in [LT,GT] and other.comp in [LE,GE])
        
    
    def __cmp__(self,other):
       if self.coeff==other.coeff and self.comp==other.comp:
           return 0
       return 1
                

# The multiplicative procedure makes use of inequalities like t > 1, where
# t is a Mul_term.
class One_comparison:

    def __init__(self, term, comp):
        self.term = term
        self.comp = comp

    def __str__(self):
        return str(self.term) + ' ' + comp_str[self.comp] + ' 1'

    def __repr__(self):
        return self.__str__()
        


###############################################################################
#
# DATA STRUCTURE FOR THE HEURISTIC PROCEDURE
#
###############################################################################

#
# The procedure keeps track of the following data:
#   o the original list of terms
#   o a name of the form "a_i" for each term
#   o the total number of terms
#   o for each i, any known comparison of a_i with 0
#   o for each i < j, any known comparisons between a_i and c * a_j for some c
#   o a flag, 'verbose', for printing
#   o a flag, 'changed', to indicate whether anything has been learned in
#     since the flag was last set to False



class Heuristic_data:

    #Each Heuristic_data has:
    #  terms[i]: ith subterm of hypotheses (in original variables)
    #  name_defs[i]: definition of a_i (using Vars and other a_js)
    #  num_terms = len(terms)
    #  zero_comparisons[i]: Zero_comparison_data corresponding to a_i COMP 0
    #  term_comparisons[i,j]: List of Comparison_data's between a_i, a_j

    # __init__ takes a list of hypotheses, each assumed to be Zero_comparison 
    # like t > 0, where t is assumed to be in canonical form.
    #
    # It stores a list of all the subterms and creates names for them,
    # and then stores the relationship between the names.
    
    # takes a list of terms, stores a list of all subterms and 
    # creats names for them
    def __init__(self, hypotheses, function_information = [], verbose=True):
        self.verbose = verbose
        
        self.function_information = function_information
        
        # initialize term comparisons
        self.term_comparisons = {}
        
        #Stores terms that are equal to 0, that contain information beyond variable definitions.
        self.zero_equations = []
        

        # make the names
        hterms = [h.term for h in hypotheses]
        self.terms, self.name_defs = make_term_names(hterms)
        self.num_terms = len(self.terms)

        # store hypotheses as zero comparisons
        self.zero_comparisons = {0 : Zero_comparison_data(GT, HYP)}
        equals_0 = []
        for h in hypotheses:
            i = self.terms.index(h.term)
            if i in self.zero_comparisons.keys():
                icomp = self.zero_comparisons[i].comp
                if ((icomp == LT and h.comp in [GE,GT]) or (icomp==GT and h.comp in [LE,LT])
                      or (icomp == LE and h.comp==GT) or (icomp==GE and h.comp==LT)):
                    self.raise_contradiction(HYP)
                    return
                elif (icomp==LE and h.comp==GE) or (icomp==GE and h.comp==LE): #learn equality. Not handled yet.
                    equals_0.append(i)
                elif (icomp in [LE,GE] and h.comp in [LT,GT]):
                    self.zero_comparisons[i]=Zero_comparison_data(h.comp,HYP)
            else:
                self.zero_comparisons[i] = Zero_comparison_data(h.comp, HYP)
                
            if isinstance(self.name_defs[i],Add_term) and len(self.name_defs[i].addpairs)==2: #a_i = cj*a_j + ck*a_k comp 0. Make a term_comparison
                #print 'addpair:',self.name_defs[i]
                pairj,pairk = self.name_defs[i].addpairs[0],self.name_defs[i].addpairs[1]
                j,k = pairj.term.index,pairk.term.index
                cj,ck = pairj.coeff,pairk.coeff
                comp = self.zero_comparisons[i].comp
                if j>k:
                    j,k,pairj,pairk,cj,ck = k,j,pairk,pairj,ck,cj
                    
                c = -ck/cj
                if cj<0:
                    comp = comp_reverse(comp)
                self.learn_term_comparison(j,k,comp,c,HYP)
            
            elif isinstance(self.name_defs[i],Mul_term) and len(self.name_defs[i].mulpairs)==1 and Fraction(self.name_defs[i].mulpairs[0].exp).numerator%2==0:
                self.learn_zero_comparison(i,GE,HYP)


        for i in equals_0:
            self.learn_zero_equality(i,HYP)

        # print information
        if self.verbose:
            print
            print "Definitions:"
            for i in range(self.num_terms):
                print IVar(i), '=', self.name_defs[i]
                print '  In other words:', IVar(i), '=', self.terms[i]
            print
            print("Hypotheses:")
            for i in range(self.num_terms):
                if i in self.zero_comparisons.keys():
                    print self.zero_comparisons[i].to_string(IVar(i))
                    print '  In other words:', \
                        self.zero_comparisons[i].to_string(self.terms[i])

            print
        
        #If the input had anything of the form  a^(p/q) where q is even,
        #We can assume a is positive.
        for t in self.name_defs.keys():
            s = self.name_defs[t]
            if isinstance(s,Mul_term):
                for m in s.mulpairs:
                    if ((isinstance(m.exp,Fraction) and m.exp.denominator%2==0) or
                      (isinstance(m.exp,float) and Fraction(m.exp).denominator%2==0)):
                        self.learn_zero_comparison(m.term.index,GE,HYP)
            
    
    def get_index_of_name_def(self,term):
        for k in self.name_defs.keys():
            if self.name_defs[k]==term:
                return k
        return None
    
    #Returns a new instance of an identical Heuristic_data        
    def duplicate(self):
        H = Heuristic_data([],self.verbose)
        H.terms = list(self.terms)
        H.num_terms = self.num_terms
        H.function_information = list(self.function_information)
        
        for c in self.zero_comparisons.keys():
            H.zero_comparisons[c] = self.zero_comparisons[c]
            
        for c in self.term_comparisons.keys():
            H.term_comparisons[c] = self.term_comparisons[c]
            
        for c in self.name_defs.keys():
            H.name_defs[c] = self.name_defs[c]
        return H

    #If there is data on whether a_i is > 0 or < 0, returns the sign. Otherwise, returns 0
    def sign(self, i):
        if i in self.zero_comparisons.keys():
            comp = self.zero_comparisons[i].comp
            if comp == GT:
                return 1
            elif comp == LT:
                return -1
            else:
                return 0
        else:
            return 0
    
    #If there is data on whether a_i is >= 0 or <=0, returns the sign. Otherwise, returns 0    
    def weak_sign(self,i):
        if i in self.zero_comparisons.keys():
            comp = self.zero_comparisons[i].comp
            if comp == GT or comp==GE:
                return 1
            elif comp == LT or comp==LE:
                return -1
            else:
                return 0
        else:
            return 0
    
    #Removes redundant information from term_comparisons.
    #Not currently used: empirically, there is little to no redundant info to clean.
    def clean_comparison_data(self):
        print 'cleaning!'
        print self.term_comparisons
        for (i,j) in self.term_comparisons.keys():
            if self.sign(j)==0:
                continue
            #Otherwise, there should be at most one > and one < comparison.
            comps = self.term_comparisons[i,j]
            if len(comps)>4:
                print 'trouble! we have more than 4 comps between',i,j
            dirs = [c.comp for c in comps]
            if dirs.count(LE)+dirs.count(LT) > 1:
                print 'removing < data from',comps
                if H.sign(j)>0: #want the one with smallest coeff
                    for c in comps:
                        if c.comp in [LE,LT] and not all(c.le(d) for d in comps):
                            comps.remove(c)
                elif H.sign(j)<0:
                    for c in comps:
                        if c.comp in [LE,LT] and not all(c.ge(d) for d in comps):
                            comps.remove(c)
                print 'now =',comps
            if dirs.count(GE)+dirs.count(GT) > 1:
                print 'removing > data from',comps
                if H.sign(j)>0: #want the one with smallest coeff
                    for c in comps:
                        if c.comp in [GE,GT] and not all(c.ge(d) for d in comps):
                            comps.remove(c)
                elif H.sign(j)<0:
                    for c in comps:
                        if c.comp in [GE,GT] and not all(c.le(d) for d in comps):
                            comps.remove(c)
                print 'now =',comps
            self.term_comparisons[i,j]=comps
            

    def raise_contradiction(self, provenance):
        raise Contradiction('Contradiction!')
    
    #Learn a_i = 0.
    #Eliminates a_i from all stored data
    def learn_zero_equality(self,i,provenance):
        if self.name_defs[i] in self.zero_equations or IVar(i) in self.zero_equations:
            return
        print "Learning equality:",IVar(i),"= 0"
        #self.name_defs[i] = zero
        #turn all comparisons with a_i to zero_comparisons
        for j in range(0,i):
            if (j,i) in self.term_comparisons.keys():
                comps = self.term_comparisons[j,i]
                for c in comps:
                    self.learn_zero_comparison(j,c.comp,provenance)
        for j in range(i+1,self.num_terms):
            if (i,j) in self.term_comparisons.keys():
                comps = self.term_comparisons[i,j]
                for c in comps:
                    self.learn_zero_comparison(j,comp_reverse(c.comp),provenance)
                    
                    
        for k in self.name_defs.keys():
            if k == i:
                continue
            ak = self.name_defs[k]
            if isinstance(ak,Mul_term):
                for c in ak.mulpairs:
                    if c.term.index == i: #ak = 0
                        if c.exp < 0:
                            raise Exception("Trying to divide by 0!")
                        self.learn_zero_equality(k,provenance)
            elif isinstance(ak,Add_term):
                for c in ak.addpairs:
                    if c.term.index == i:
                        ak.addpairs.remove(c)
                if len(ak.addpairs)==0:
                    self.learn_zero_equality(ak.index,provenance)
        
        t = self.name_defs[i]            
        if isinstance(t,Add_term): #0 = c*a_1+d*a_2+...
            if len(t.addpairs)==1:
                self.learn_zero_equality(t.addpairs[0].term.index,provenance)
        
        if not isinstance(t,Var):
            self.zero_equations.append(t)
        else:
            self.zero_equations.append(IVar(i))
                
    # Adds information about how a_i compares to 0.
    # If the new information contradicts old, raises contradiction.
    def learn_zero_comparison(self, i, comp, provenance):
        if i in self.zero_comparisons.keys():
            old_comp = self.zero_comparisons[i].comp
            if ((old_comp == GE and comp == LE) or 
                (old_comp == LE and comp == GE)):
                self.learn_zero_equality(i)
                #raise Error('Learn equality - not handled yet')
            elif ((old_comp in [GE, GT] and comp in [LE, LT]) or
                  (old_comp in [LT, LE] and comp in [GE, GT])):
                if self.verbose:
                    c = Zero_comparison_data(comp, provenance)
                    print 'Learned:', c.to_string(IVar(i))
                    print '  In other words:', c.to_string(self.terms[i])
                self.raise_contradiction(provenance)
            elif ((old_comp == GE and comp == GT) or 
                  (old_comp == LE and comp == LT)):
                # new fact is stronger; drop old
                del self.zero_comparisons[i]
            else:    # new fact is weaker
                return

        # add new comparison
        self.zero_comparisons[i] = Zero_comparison_data(comp, provenance)
        self.changed = True
        if self.verbose:
            print 'Learned:', self.zero_comparisons[i].to_string(IVar(i))
            print '  In other words:', \
                   self.zero_comparisons[i].to_string(self.terms[i])
    
    #Learns a_i = coeff * a_j
    def learn_term_equality(self,i,j,coeff,provenance):
        if i==j:
            if coeff != 1:
                self.learn_zero_equality(i,provenance)
            return
        
        self.zero_equations.append(IVar(i) - IVar(j) * coeff)
        

    # new_comp is Comparison_data to potentially be added. a_i comp coeff a_j,
    #     but this method does not need to know i or j.
    # old_comps is list of comparisons of the same direction as new_comp
    # sign is +1 if a_j positive, -1 if a_j negative, 0 if a_j unknown
    # changes old_comps. returns True if changes are made, False otherwise               
    def make_new_comps(self, new_comp, old_comps, sign):
        #print 'make new comps fed:',new_comp,old_comps,sign
        if not old_comps: #no comparisons in this direction.
            old_comps.append(new_comp)
            return True
        
        # If new_comp is already in there, no changes needed.    
        if new_comp in old_comps:
            return False
            
        if sign == 0: #We do not know the sign of a_j
            if len(old_comps) == 1: # Only one element in old_comps, so new_comp has new info
                old_comps.append(new_comp)
                return True
                
            # Otherwise, there are two comps in old_comps.
            # See if new_comp is stronger or weaker than both.
            
            lt_all, gt_all = all(new_comp.le(c) for c in old_comps),all(new_comp.ge(c) for c in old_comps)
            if lt_all:
                for i in range(2):
                    if old_comps[i].le(old_comps[1-i]):
                        old_comps.pop(i)
                        old_comps.append(new_comp)
                        return True
                        
            elif gt_all:
                for i in range(2):
                    if old_comps[i].ge(old_comps[1-i]):
                        old_comps.pop(i)
                        old_comps.append(new_comp)
                        return True
                        
            return False
        
        #Otherwise, we do know the sign of a_j. There will only be one element in old_comps now.
        #new_comp should be that element if it is stronger than the alternatives in the proper direction.
        p1 = (new_comp.comp in [LE,LT] and ((sign == 1 and all(new_comp.le(c) for c in old_comps)) or (sign == -1 and all(new_comp.ge(c) for c in old_comps))))
        p2 = (new_comp.comp in [GE,GT] and ((sign == 1 and all(new_comp.ge(c) for c in old_comps)) or (sign == -1 and all(new_comp.le(c) for c in old_comps))))
        if p1 or p2:
            #print 'only one comp. sign = ',sign,'new comp = ',new_comp, 'old_comps = ',old_comps
            while len(old_comps)>0:
                old_comps.pop()
            old_comps.append(new_comp)
            return True
            
        return False


    # for each pair i, j, there may be up to four comparisons of the form
    #     a_i comp c * a_j
    # if the sign of a_j is known, there are at most two such comparisons
    #
    # to do: after signs are learned, clean up list of comparisons 
    # also to do: for now, we don't handle the case where
    #   a_i <= c * a_j and a_i >= c * a_j 
    # are both known, yielding an equality.
    # also: from a_i comp c * a_j and a_i comp c' * a_j, we can sometimes
    #   infer a_j = 0, but we don't currently handle this
    # 
    # also: don't bother with e.g. a_i > 2 a_j if this already follows from
    #   sign information?
    def learn_term_comparison(self, i, j, comp, coeff, provenance):

        # swap i and j if necessary, so i < j
        if i >= j:
            i, j, coeff = j, i, Fraction(1, Fraction(coeff))
            if coeff > 0:
                comp = comp_reverse(comp)
                

        #See if we can get any zero_comparisons from 1 comp c*a_j.
        if i==0:
            if coeff > 0 and comp in [LE,LT]: #a_j >= 1/c > 0
                self.learn_zero_comparison(j,GT,provenance)
            elif coeff < 0 and comp in [LE,LT]: #a_j <= 1/c < 0
                self.learn_zero_comparison(j,LT,provenance)

        if (i, j) in self.term_comparisons.keys():
            comp_list = self.term_comparisons[i, j]
        else:
            comp_list = []
            
        lcomps = [c for c in comp_list if c.comp in [LT, LE]]
        gcomps = [c for c in comp_list if c.comp in [GT, GE]]
        learned = False


        #replacement for case_by_case code
        new_comp_data = Comparison_data(comp,coeff,provenance)
        old = str(lcomps)+","+str(gcomps)
        if comp in [LT, LE]:
            learned = self.make_new_comps(new_comp_data,lcomps,self.sign(j))
            #print learned,lcomps
            
        elif comp in [GT, GE]:
            learned = self.make_new_comps(new_comp_data,gcomps,self.sign(j))
            #print learned,gcomps
            
        if learned:
            self.term_comparisons[i, j] = lcomps + gcomps
            self.changed = True
            if self.verbose:
                #c = Comparison_data(comp, coeff, provenance)
                print 'Learned:', new_comp_data.to_string(IVar(i), IVar(j))
                print '  In other words:', \
                       new_comp_data.to_string(self.terms[i], self.terms[j])

        # check for inconsistency
        lcoeffs = [c.coeff for c in lcomps]
        gcoeffs = [c.coeff for c in gcomps]
        if lcoeffs and gcoeffs:
            min_lcoeff = min(lcoeffs)
            min_gcoeff = min(gcoeffs)
            max_lcoeff = max(lcoeffs)
            max_gcoeff = max(gcoeffs)
            min_lcomp = next((c for c in lcomps if c.coeff == min_lcoeff))
            max_gcomp = next((c for c in gcomps if c.coeff == max_gcoeff))
            max_lcomp = next((c for c in lcomps if c.coeff == max_lcoeff))
            min_gcomp = next((c for c in gcomps if c.coeff == min_gcoeff))
        
            if self.sign(j) == 1:
                if (min_lcoeff < max_gcoeff or
                    (min_lcoeff == max_gcoeff and
                     (min_lcomp.comp == LT or max_gcomp.gcomp == GT))):
                    self.raise_contradiction(provenance)
            elif self.sign(j) == -1:
                if (max_lcoeff > min_gcoeff or
                    (max_lcoeff == min_gcoeff and
                     (min_lcomp.comp == LT or max_gcomp.gcomp == GT))):
                    self.raise_contradiction(provenance)
                    
            else:
                if ((min_lcoeff < max_gcoeff or
                    (min_lcoeff == max_gcoeff and
                     (min_lcomp.comp == LT or max_gcomp.gcomp == GT)))
                    and
                    (max_lcoeff > min_gcoeff or
                    (max_lcoeff == min_gcoeff and
                     (min_lcomp.comp == LT or max_gcomp.gcomp == GT)))):
                    self.raise_contradiction(provenance)
                    

