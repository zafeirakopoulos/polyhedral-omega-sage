# IMPORTANT This is only for experimenting. Not a stable version.
# Updated for Python3 from the original implementation

#https://github.com/zafeirakopoulos/polyhedral-omega-sage
#Copyright (C) Felix Breuer, Zafeirakis Zafeirakopoulos 2013-2024. All rights reserved.

import collections
# from UserDict import DictMixin

from sage.all_cmdline import *

# define sage constants
_0 = Integer(0)
_1 = Integer(1)


"""A naive linear algebra library implementing vector and matrix operation on tuples.

Curiously, this is faster than Sage's builting matrix and vector classes in some instances, especially, when dealing with lots of small matrices instead of few big matrices. Also, implements basic operations on lattice vectors such as converting lattice vectors into primitive vectors and checking if vectors are forward wrt. the lexicographic orientation.
"""

from sage.all_cmdline import *  

def mvv(v,w):
    """Compute the scalar product of two vectors v and w."""
    return sum(( vi * wi for (vi,wi) in zip(v,w) ))

def msv(s,v):
    """Multiply all entries of the vector v with the scalar s."""
    return tuple(( s * vi for vi in v ))

def svv(v,w):
    """Sum two vectors v and w."""
    return tuple(( vi + wi for (vi,wi) in zip(v,w) ))

def mmv(m,v):
    """Multiply a matrix m with a vector v.

    Matrices are represented as a tuple of rows."""
    return tuple(( svv(mi,v) for mi in m ))

def vector_is_forward(v):
    """Checks if a vector is forward, i.e., first non-zero coordinate is positive."""
    for vi in v:
        if vi != 0:
            return vi > 0
    return True

def intify_v(v):
    """Takes a rational vector v and returns a positive multiple of v that is integer.

    If the smallest possible multiple of v that is integer is required, apply prim_v afterwards. Return value is a Sage tuple of Integers."""
    denominators = [ vi.denominator() for vi in v ]
    l = lcm(denominators)
    return tuple((Integer(vi * l) for vi in v))

def intify_m(A):
    """Takes a Sage matrix and returns a multiple that is integer."""
    d = A.dimensions()
    denominators = [ A[i,j].denominator() for i in range(d[0]) for j in range(d[1])]
    l = lcm(denominators)
    return l*A

def lex_cmp(v,w):
    """Compare two vectors v, w lexicographically. v, w must be of same length."""
    for i in range(len(v)):
        c = cmp(v[i],w[i])
        if c != 0:
            return c
    return 0

def prim_v(v):
    """Takes an integer vector v and returns the corresponding primitive integer vector.

    The primitive integer vector corresponding to v is the least positive multiple of v that is still an integer vector.

    Arguments:
        v: An integer vector, represented as a tuple of Sage Integers.
    """
    d = abs(gcd(v))
    if d == 1:
        return v
    else:
        return tuple((vi/d for vi in v))

def prim(V):
    """Takes a tuple of integer vectors and applies prim_v to each of them."""
    return tuple(( prim_v(v) for v in V ))

def is_integral(v):
    return reduce(lambda a,b: a and b, [vi.is_integral() for vi in v])

def fract_simple(v):
    #res = []
    #for vi in v:
    #    res.append(vi - floor(vi))
    #return res
    return tuple(( vi - floor(vi) for vi in v ))


def sageify(arg):
    """Takes a nested tuple and converts all ints therein into Sage Integers."""
    if type(arg) == tuple:
        return tuple(( sageify(e) for e in arg ))
    elif type(arg) == int:
        return Integer(arg)
    elif type(arg) == list:
        return [ sageify(e) for e in arg ]
    elif type(arg) == Integer:
        return arg
    elif type(arg) == Rational:
        return arg
    elif type(arg) == sage.symbolic.expression.Expression:
        try:
            return IntegerRing()(arg)
        except:
            try:
                return RationalField()(arg)
            except:
                return arg
    #elif type(arg) == Matrix_rational_dense:
    #    return tupleize(arg)
    #elif type(arg) == Matrix_integer_dense:
    #    return tupleize(arg)
    else:
        raise TypeError("Type %s is not supported by sageify." % str(type(arg)))

def tupleize(arg):
    if type(arg) == sage.matrix.matrix_rational_dense.Matrix_rational_dense or type(arg) == sage.matrix.matrix_integer_dense.Matrix_integer_dense:
        return tuple((tupleize(row) for row in arg.rows()))
    elif type(arg) == sage.modules.vector_rational_dense.Vector_rational_dense or tupe(arg) == sage.modules.vector_integer_dense.Vector_integer_dense:
        return tuple((vi for vi in arg))
    else:
        raise TypeError("Type %s is not supported by sageify." % str(type(arg)))

def solve_linear_equation_system_over_integers(A,b):
    """Takes a Sage matrix A and a Sage vector b and solves the system Ax = b over the integers.

    Returns a solution as a Sage integer vector.

    Arguments:
        A: An integer matrix, given as a Sage object. A should be a matrix over ZZ! If A is a matrix over QQ, but with integral entries, then the Smith form will give unexpeceted results! For convenience, this function coerces matrices over QQ into matrices over ZZ, however.
        b: An integer vector, given as a Sage object.
    """
    A = column_matrix(ZZ,A.columns())
    S, Uinv, Vinv = A.smith_form()
    n = A.ncols()
    m = A.nrows()
    p = Uinv * b
    q = vector([ p[i]/S[i][i] for i in range(m) ] + [ 0 for i in range(n-m)],ZZ)
    r = Vinv * q
    return r

class LinearDiophantineSystem(object):

    def __init__(self,A,b,E=None,optb=None):
        """Creates a new LinearDiophantineSystem Ax >=^E b, x >= 0 for a given matrix A, a right-hand side b and a list E of flags indicating whether the corresponding row is an inequality or an equation. 

        The class LinearDiophantineSystem can be used to compute symbolic cone and/or rational function representations of the set of all non-negative integral solutions to the given linear system. The parameters A,b,E cannot be modified once the LinearDiophantineSystem has been constructed. The methods for solving the system, symbolic_ones, fundamental_parallelepipeds, and rational_function_string, each cache the results of their computations so that they can be run several times and the computation is done only once.

        Arguments:
            A: An integer matrix represented as a sequence of rows. Entries can be ints or Sage Integers.
            b: An integer vector, represented as a sequence. Entries can be ints or Sage Integers.
            E: A list with 0-1 entries which encodes with rows are equalities. (1 means equality, 0 means inequality.) If E is None, then all constraints are assumed to be inequalities, i.e., E is constant 0.
        """
        if E == None:
            E = [ 0 for i in range(len(A))]
        self._A = A
        self._b = b
        self._E = E
        self._cone = SymbolicCone.macmahon_cone(A,b)
#         print self._cone
        self._symbolic_cones = None
        self._symbolic_cones_evaluated = None
        self._fundamental_parallelepipeds = None
        self._rational_function = None
        self._optimization_bound = optb
        
    def symbolic_cones(self,non_iterations=0,logging=False):
        """Computes a representation of the set of all non-negative integral solutions as a linear combination of symbolic cones.

        Returns a CombinationOfCones representing the result.
        """
        if self._symbolic_cones == None:
            E = list(self._E)
            E.reverse() # reverse, because we want to eliminate the last rows
            self._symbolic_cones = CombinationOfCones({self._cone: Integer(1)})
            i = 0
            for e in E[non_iterations:]:
                self._symbolic_cones = self._symbolic_cones.map_cones(lambda c: c.eliminate_last_coordinate(equality=e))
                if logging:
                    i = i + 1
                    d = len(self._A[0])
                    max_cones = binomial(d+i,d)
                    num_cones =len(self._symbolic_cones)
                    print("iteration %d of %d: %d cones (%.2f%% of theoretical maximum %d) " % (i,len(E),num_cones,(float(num_cones)/max_cones)*100,max_cones))
                    print(self._symbolic_cones)
        return self._symbolic_cones


    def fundamental_parallelepipeds(self):
        """For each of the cones in the solution returned by symbolic_cones, this method enumerates all lattice points in the corresponding fundamental_parallelepipeds.

        Returns a dictionary, mapping cones to the set of lattice points in the fundamental_parallelepipeds. Each set of lattice point is represented as a list of tuples of Sage Integers.
        """
        if self._fundamental_parallelepipeds == None:
            cones = self.symbolic_cones()
            self._fundamental_parallelepipeds = {}
            for cone in cones.keys():
                points = cone.enumerate_fundamental_parallelepiped()
                self._fundamental_parallelepipeds[cone] = points
        return self._fundamental_parallelepipeds


    def get_for_cut(self,b):
        elds = self._symbolic_cones.copy()
        elds.eval_at(self._optimization_bound,b)
        nlds = elds.map_cones(lambda c: c.eliminate_last_coordinate())
#         print nlds
        fundamental_parallelepipeds = {}
        for cone in nlds:
            points = cone.enumerate_fundamental_parallelepiped()
            fundamental_parallelepipeds[cone] = points
        rf = nlds.rational_function(fundamental_parallelepipeds)
        if rf!=0:
            ed = {}
            genz =  rf.parent().gens()
            for i in genz:
                ed[i]=1
            return rf.subs(ed), rf
        else:
            return 0,0

    
class SymbolicCone():
# class SymbolicCone(collections.Hashable):
    """The vertex description of a simplicial symbolic cone.

    The vertex decription of a simplicial cone consists of its apex (which may be rational), the matrix of generators (which must be integral and linearly independent) and a vector of boolean flags indicating which faces are open and closed.

    SymbolicCones are immutable and hashable to facilitate using them as keys in a dictionary.

    This class implements intersecting a SymbolicCone with a coordinate half-space, enumerating the fundamental parallelepiped of a SymbolicCone, computing an inequality description of the symbolic cone and flipping a cone "forward".

    Attributes:
        generators: The generators of the cone, given as a tuple of integer vectors. Vectors are tuples of Sage integers. Generators must be linearly independent. Read-only.
        apex: The apex of the cone, given as a tuple of Sage rationals. Read-only.
        openness: A tuple of booleans, indicating which faces of the cone are open. If openness[i] == 1, the coefficient of the i-th generator is strictly bigger than one, so that the opposite face is open. Conversely, if penness[i] == 0, the coefficient of the i-th generator is strictly bigger than one, so that the opposite face is open.
        dimension: Dimension of the cone, that is, the number of generators. Read-only.
        ambient_dimension: The dimension of the ambient space in which the cone lies, that is, the length of each generator. Read-only.
    """

    def __init__(self, generators, apex, openness=None, do_canonicalize=True):
        """Initializes the SymbolicCone with the given generators, apex and openness. 

        If openness is not given (or None), then the cone is closed. Arguments have to be as specified in the class description.
        """
        # TODO: Check for TypeErrors and ValueErrors. Is the performance overhead for these checks acceptable? Also if we verify linear independence of generators?
        self._dimension = len(generators)
        self._ambient_dimension = len(generators[0])
        self._generators = tuple( tuple( sageify(i) for i in g) for g in generators)
        self._apex = tuple( sageify(i) for i in apex)
        if openness == None:
            self._openness = tuple([ 0 for i in range(self.dimension)])
        else:
            self._openness = openness
        if do_canonicalize:
            self.canonicalize()
        self._qint= None
        self._sk = None
        self._o = None
        self._fundpar = None
        self._Wprime = None

    def copy(self):

        ret = SymbolicCone(tuple([ tuple([i for i in g]) for g in self._generators]), tuple([ a for a in self._apex]), tuple([o for o in self._openness]), do_canonicalize=True)

        #ret._qint = self._qint
        #ret._qsummand = self._qsummand
        #ret._sk = self._sk 
        #ret._o = self._o
        #ret._fundpar = self._fundpar
        #ret._Wprime = self._Wprime

        return ret

    def subs(self, d):
        self._apex = tuple( sageify(i.subs(d)) if i.parent()==SR else i for i in self._apex)
        self._generators = tuple( tuple( sageify(j.subs(d))  if j.parent()==SR else j for j in i )  for i in self._generators)
        #self._qint = tuple( sageify(i.subs(d)) if i.parent()==SR else i for i in self._qint)
        #self._qsummand = tuple( sageify(i.subs(d)) if i.parent()==SR else i for i in self._qsummand)
        return self

    @property
    def dimension(self):
        return self._dimension
    
    @property
    def ambient_dimension(self):
        return self._ambient_dimension
    
    @property
    def generators(self):
        return self._generators
    
    @property
    def apex(self):
        return self._apex

    @property
    def openness(self):
        return self._openness

    def __hash__(self):
        """Computes hash value of self."""
        return tuple([self._generators,self._apex,self._openness]).__hash__()

    def __eq__(self,other):
        """Two cones are equal if they have equal generators, apex and openness."""
        return self.generators == other.generators and self.apex == other.apex and self.openness == other.openness

    def __rmul__(self,other):
        """Multiplications i * c where i is an integer and c a SymbolicCone."""
        return self.__mul__(other)

    def __mul__(self,other):
        """Multiplication of SymbolicCone with an integer returns a CombinationOfCones.

        Arguments:
            other: An integer, represented as an int or a Sage Integer."""
        if type(other) == Integer:
            return CombinationOfCones({self:other})
        elif type(other) == int:
            return self * Integer(other)
        else:
            return NotImplemented

    def __add__(self,other):
        if type(other) == SymbolicCone:
            C = CombinationOfCones(self)
            C += other
            return C
        else:
            return NotImplemented

    def __repr__(self):
        return "[ Cone: generators = %s, apex = %s, openness = %s ]" % (self.generators.__repr__(), self.apex.__repr__(), self.openness.__repr__())

    def canonicalize(self):
        """Permutes generators of self so that they are in lexicographic order."""
        # We have to permute the generators and the openness vector with the same permutation.
        # To do this, we zip both lists and then permute according to the first argument.
#         pairs = zip(self._generators,self._openness)
#         pairs.sort(cmp = lambda x,y: lex_cmp(x[0],y[0]))
#         gens, opens = zip(*pairs) # zip also does unzip!
        pairs = list(zip(self._generators,self._openness))
#         pairs.sort(cmp = lambda x,y: lex_cmp(x[0],y[0]))
        pairs.sort()
        gens, opens = zip(*pairs) # zip also does unzip!
        self._generators = tuple(gens)
        self._openness = tuple(opens)

    def generator_matrix(self):
        """Returns a matrix with generators as columns."""
        return column_matrix(ZZ,self._generators)

    def snf_divisors(self):
        """Computes the list of elements on the diagonal of the Smith Normal Form of the matrix of generators."""
        smith_form = self.generator_matrix().smith_form()[0]
        return [smith_form[i][i] for i in range(self.dimension)]

    def index(self):
        """Computes the index (the determinant) of self."""
        return prod(self.snf_divisors())

    def flip(self):
        # we have to use lists instead of generators here, because zip does not work for generators
        J = [ not vector_is_forward(v) for v in self.generators ] # 1 = backward, 0 = forward
        Jpm = [ -_1 if Ji else _1 for Ji in J ] # -1 = backward, 1 = forward
        s = prod(Jpm) # s = (-1)**(number of backward generators)
        _o = tuple(( 1 if oi != Ji else 0 for (oi,Ji) in zip(self.openness,J) ))
        _V = tuple(( msv(Jpmi, v) for (Jpmi,v) in zip(Jpm,self.generators) ))
        return s * SymbolicCone(_V,self.apex,_o)

    def eliminate_last_coordinate(self,equality=False):
        """Eliminates the last coordinate of self by intersection.

        More precisely, eliminate_last_coordinate computes a Brion decomposition of self intersected with the half-space in which the last coodinate is non-negative, and projects the result by forgetting the last coordinate. The elements of the Brion decomposition are all simplicial cones. The formula for decomposition assumes that the projection is one-to-one, i.e., the affine hull of self intersects the last-coordinate-equal-zero-hyperplane in codimension one. (This assumption holds, e.g., then the coordinate generated was introduced by MacMahon-lifting.)

        Also supports intersection with the last-coordinate-equal-zero-hyperplane instead of the half-space where the last coordinate is non-negative. To this end, the argument equality has to be set to True.

        Arguments:
            equality: True if we intersect with hyperplane instead of half-space.
        """
        # abbreviate variables
        V = self.generators
        q = self.apex
        o = self.openness
        k = self.dimension
        n = len(V[0]) - 1 # index of last coordinate
        #print "V", V
        #print "Last coornate index", n
        #print "Last coornate value", q[n]
        w = lambda j: svv(q, msv(-q[n]/(V[j][n]), V[j])) # q - q[n]/(V[j][n]) * V[j]
        sgqn = 1 if q[n] >= 0 else -1

        def g(i,j):
            if i == j: # TODO: check if this makes sense for e == 1 as well
                return msv(-1,V[j]) if q[n] >= 0 else V[j]
            else:
                return msv(sgqn, svv( msv(V[i][n], V[j]), msv(-V[j][n], V[i]))) # sg(qn) * ( V[i][n] * V[j] - V[j][n] * V[i] )
        if not equality:
            G = lambda j: prim(( g(i,j)[:-1] for i in range(k) ))
        else:
            G = lambda j: prim(( g(i,j)[:-1] for i in range(k) if j != i ))
        def _o(j):
            if equality: # drop j-th element
                return o[:j] + o[j+1:]
            else: # replace j-th element with zero
                return o[:j] + (0,) + o[j+1:]
        def Bplus():
            return CombinationOfCones.sum(( SymbolicCone(G(j), w(j)[:-1], _o(j)) for j in range(k) if V[j][n] > 0 ))
        def Bminus(): # the Bminus in the paper is this Bminus + Cprime
            return CombinationOfCones.sum(( SymbolicCone(G(j), w(j)[:-1], _o(j)) for j in range(k) if V[j][n] < 0 ))
        def Cprime():
            return CombinationOfCones(SymbolicCone(prim([v[:-1] for v in V]), q[:-1], o))

        n_up = len([Vj for Vj in V if Vj[n] > 0])
        n_down = len([Vj for Vj in V if Vj[n] < 0])
        n_flat = k - n_up - n_down
        if not equality:
            if q[n] < 0:
                B = Bplus()
            else: # if q[n] >= 0
                B = Bminus() + Cprime()
            # TODO: optimization: if we have a choice, take decomposition with fewer cones
        else: # if equality
            if q[n] < 0 or (q[n] == 0 and exists(range(k),lambda j: V[j][n] > 0)[0]):
                B = Bplus()
            elif q[n] > 0 or (q[n] == 0 and exists(range(k),lambda j: V[j][n] < 0)[0]):
                B = Bminus()
            else: # q[n] == 0 and forall(range(k), lambda j: V[j][n] == 0)[0]
                B = Cprime()

        #print "intermediate result before flip", B
        result = B.map_cones(lambda C: C.flip())
        #print "yields result", result
        return result


    def enumerate_fundamental_parallelepiped(self):
        """Returns a list of all integer points in the fundamental parallelepiped of self.

        The integer points in the list are represented as tuples of Sage integers. Their number is self.index(). Note that this list may be exponentially large; its computation may therefore take a long time and consume a lot of memory.
        """
        k = self.dimension
        d = self.ambient_dimension
        V = self.generator_matrix()
        q = vector(self.apex,SR)
        p = vector([0 for i in range(d)],SR)
        #if k < d: # this is only relevant if we had equality constraints during elimination
        #    # find an integer point in the affine span
        #    A,b = self.inequality_description_of_affine_hull()
        #    p = solve_linear_equation_system_over_integers(A,b)
        #    if not is_integral(p):
        #        return []
        # note: in Sage the Smith form is UVW = S, whereas in the draft we use V=USW.
        S,Uinv,Winv = V.smith_form()
        s = [S[i][i] for i in range(k)] # we don't need the last d-k 1s: + [1 for i in range(d-k)]
        sk = s[k-1]
        sprime = [Integer(sk / si) for si in s]
        qhat = Uinv * (q - p)
        Wprime = tuple((tuple(( Winv[j,i] * sprime[i] for i in range(k))) for j in range(k))) # Wprime = Winv * Sprime, in the paper
        # DEBUG: Wprimem = matrix(ZZ,Wprime) # same matrix as a Sage object
        qtrans = [ sum([ - Wprime[j][i] * qhat[i]  for i in range(k)]) for j in range(k) ] # qtrans = - Winv * Sprime * qhat, in the paper
        qfrac = fract_simple(qtrans)
        qint = [ floor(qi) for qi in qtrans ]
        # DEBUG: qintv = vector(ZZ,qint)
        qsummand = tuple((qi for qi in sk * q + V * vector(qfrac) ))
        # DEBUG: qsummandv = vector(ZZ,qsummand)
        o = [ (self.openness[j] if qfrac[j] == 0 else 0) for j in range(k) ]
        cpl = [ [ i for i in range(s[j])] for j in range(k)]

        P = cartesian_product( cpl )

        self._qint=sageify(qint)
        self._qsummand = sageify(qsummand)
        self._sk = sageify(sk)
        self._o = o
        self._fundpar = P
        self._Wprime = Wprime
        return [ self.transform_integral(p) for p in P]

    def transform_integral(self,z):
        innerRes = []
        j = 0
        for qj in self._qint: # qint has k entries
            inner = 0
            i = 0
            for zi in z: # z should have k entries
                inner += self._Wprime[j][i] * zi # Wprime[i,j] * vj
                # the following is optional, depending on performance
                #inner = inner % sk
                i += 1
            inner += qj
            inner = inner % self._sk
            # inner has to be modified according to o
            if inner == 0 and self._o[j]:
                inner = self._sk
            innerRes.append(inner)
            j += 1
        outerRes = []
        for l in range(self.ambient_dimension):
            outer = 0
            j = 0
            for innerResi in innerRes:
                outer += self.generator_matrix()[l,j] * innerResi
                j += 1
            outerRes.append(outer) # outerRes is an integral vector
        return tuple(( (ai + bi).divide_knowing_divisible_by(self._sk) for (ai,bi) in zip(outerRes, self._qsummand) ))


    def univariate_rational_function(self):

        fundamental_parallelepiped = [ self.transform_integral(v) for v in self._fundpar]

        d = self.ambient_dimension
        RFF = PolynomialRing(QQ,["t"]).fraction_field()
        t = RFF.gen(0)
        self._denominator = prod([ 1-e**(t*sum(g)) for g in self._generators])
#         print self._generators
#         print self._denominator
#         print self._generators

        self._numerator = sum([ e**(t*sum(p)) for p in fundamental_parallelepiped])
        self._rational_function = self._numerator/self._denominator
        return self._rational_function

    def inequality_description_of_affine_hull(self):
        k = self.dimension
        d = self.ambient_dimension
        if d == k: 
            # as we assume that V is full rank, this implies that the cone is full dimensional
            # therefore the system describing the affine hull is empty
            return ([],[])
        V = self.generator_matrix()
        q = vector(self.apex,SR)
        P, L, U = V.LU()
        A = L**(-1)*P**(-1)
        Ap = A[-(d-k):]
        b = Ap * q
        # this last part makes sure that the system Ax=b is integral
        m = Ap.nrows()
        multipliers = [ lcm([ Ap[i,j].denominator() for j in range(d) ] + [b[i].denominator()]) for i in range(m) ]
        S = diagonal_matrix(multipliers)
        result = (S*Ap, S*b)
        return result


    @staticmethod
    def macmahon_cone(A,b):
        """Takes a linear system and returns the corresponding MacMahon cone.

        Arguments:
            A: An integer matrix represented as a tuple of rows. Entries can be ints or Sage Integers.
            b: An integer vector, represented as a tuple. Entries can be ints or Sage Integers.
            E: A 0-1 vector which encodes with rows are equalities. (1 means equality, 0 means inequality.)
        """
        if type(b) != tuple and type(b) != list:
            raise TypeError("Right-hand side b should be a tuple or list of integers, but is %s" % b.__repr__())
        _A = matrix(SR,sageify(A))
        _b = vector(SR,sageify(b))
        d = _A.ncols()

        generators = tuple(( tuple(( vij for vij in column )) for column in identity_matrix(ZZ,d).stack(_A).columns() ))
        apex = tuple( [0 for i in range(d)] + [-1 * bi for bi in _b] )
        openness = tuple((0 for i in range(d)))

        return SymbolicCone(generators, apex, openness)

    @staticmethod
    def cone_from_homogeneous_system(A):
        """Takes a matrix describing a homogeneous system of linear inequalities and returns the cone they define.

        Arguments:
            A: A matrix that defines a homogeneous linear inequality system Ax >= 0. A is assumed to be square and of full rank. A has to be a Sage matrix.
        """

        # Implementation: The columns of A^(-1) are the generators of the cone define by Ax >= 0. Of course these columns have to be brought in integer form.

        V = A**(-1)
        d = A.dimensions()[0]
        generators = V.columns()
        integer_generators = tuple((prim_v(intify_v(g)) for g in generators))
        apex = tuple((0 for i in range(d)))
        openness = tuple((0 for i in range(d)))

        return SymbolicCone(integer_generators, apex, openness)

class CombinationOfCones(dict):
    def __init__(self,*args,**kwargs):
        if len(args) == 1 and len(kwargs) == 0 and type(args[0]) == SymbolicCone:
            super(CombinationOfCones,self).__init__({args[0]: _1})
        else:
            super(CombinationOfCones,self).__init__(*args,**kwargs)

    def __add__(self,other):
        """Returns a new CombinationOfCones that is the sum of self and another SymbolicCone or CombinationOfCones."""
        if type(other) != SymbolicCone and type(other) != CombinationOfCones:
            return NotImplemented
        result = CombinationOfCones()
        result += self
        result += other
        return result

    def __mul__(self,other):
        """Returns a new CombinationOfCones that is self multiplied with a scalar factor given by other."""
        if type(other) != Integer and type(other) != int:
            return NotImplemented
        result = CombinationOfCones()
        result += self
        result *= other
        return result        

    def __iadd__(self,other):
        """Adds another SymbolicCone or CombinationOfCones to self. Updates self in-place."""
        if type(other) == SymbolicCone:
            self.add_cone(other)
        elif type(other) == CombinationOfCones:
            for cone, multiplicity in other.items():
                self.add_cone(cone,multiplicity)
        else:
            return NotImplemented
        return self

    def __imul__(self,other):
        """Multiplies self with an integer other. Updates self in-place."""
        if type(other) == Integer:
            if other == _0:
                self.clear()
            else:
                for cone in self.keys():
                    self[cone] = self[cone] * other
            return self
        elif type(other) == int:
            self.__imul__(Integer(other))
            return self
        else:
            return NotImplemented

    def __repr__(self):
        r = []
        for cone, multiplicity in self.items():
            r.append("%d * %s " % (multiplicity,cone.__repr__()) )
        return " + ".join(r)

    def add_cone(self,cone,multiplicity=_1):
        """Adds cone to this linear combination of cones.

        Self is modified in place. Multiplicity of added cone may be given. Returns self.

        Arguments:
            cone: The SymbolicCone to be added to self.
            multiplicity: The multiplicity of cone, given as an Integer.
        """
        if multiplicity != _0:
            old_m = self[cone] if cone in self else _0
            new_m = old_m + multiplicity
            if new_m == _0 and cone in self:
                del self[cone]
            else:
                self[cone] = new_m
        return self

    def map_cones(self,f):
        """Applies function f to every cone in self and returns the linear combination of results.

        f is a function taking a SymbolicCone and returning a CombinationOfCones. If self represents a combination of cones a_1 * c_1 + ... + a_k * c_k, then self.map_cones(f) returns the combination a_1 * f(c_1) + ... + a_k * f(c_k). If f(c_i) is itself a linear combination, then the distributive law is applied to flatten the sum and collect terms. map_cones not modify self, but instead returns a new CombinationOfCones instance.

        Arguments:
            f: A function of a single argument, mapping a SymbolicCone to a CombinationOfCones.
        """
        result = CombinationOfCones()
        for cone, multiplicity in self.items():
            # ensure all updates happen in-place through the use of += and *=
            combination = f(cone)
            combination *= multiplicity 
            result += combination
        return result

    @staticmethod
    def sum(gen,first=None):
        """Takes a list or generator of SymbolicCones and CombinationOfCones and returns their sum.

        Arguments:
            gen: A list or generator of SymbolicCones and CombinationOfCones. Both types can be mixed.
            first: An initial CombinationOfCones to which all elements in gen are added. First is modified in-place. If first is omitted a new empty CombinationOfCones is created.
        """
        if first == None:
            first = CombinationOfCones()
        result = first
        for c in gen:
            result += c
        return result

    def eval_at(self,x,v):
        return self.map_cones(lambda C: C.subs({x:v}))

    def copy(self):
        result = CombinationOfCones()
        for cone, multiplicity in self.items():
            # ensure all updates happen in-place through the use of += and *=
            combination = cone.copy()
            combination *= multiplicity
            result += combination
        return result

    def rational_function_string(self,fundamental_parallelepipeds):
        """Computes the symbolic_cones and the fundamental_parallelepipeds and then turns this data into a string representation of the corresponding rational function.

        Returns the rational function as a string of the form "r1 + r2 + ... + rn" where each ri is a rational function of the form "m * (p) / (q)" where p is a Laurent polynomial expanded with respect to the monomial basis and q is a polynomial written as a product of factors "(1-m)" where m is a multivariate monomial. Variables are "z1", ..., "zn" and exponentiation is written "z1**3", for example.
        """
        def stringify_cone(cone,fundamental_parallelepiped):
            d = cone.ambient_dimension
            V = cone.generators
            def stringify_monomial(z):
                return "*".join(("z%d**%d" % (i,z[i]) for i in range(d)))
            num = "+".join((stringify_monomial(t) for t in fundamental_parallelepiped))
            den = "*".join(( "(1-%s)" % stringify_monomial(c) for c in V))
            return ("(%s)/(%s)" % (num,den))
        rational_functions = []
        for cone, multiplicity in self.items():
            pi = fundamental_parallelepipeds[cone]
            rational_functions.append( "("+str(multiplicity) + ") *" + stringify_cone(cone,pi) )
        if len(rational_functions) > 0:
            self._rational_function = "+".join(rational_functions)
        else:
            self._rational_function = "0"
        return self._rational_function


    def rational_function(self,fundamental_parallelepipeds):
        """Computes the symbolic_cones and the fundamental_parallelepipeds and then turns this data into a string representation of the corresponding rational function.

        Returns the rational function as a string of the form "r1 + r2 + ... + rn" where each ri is a rational function of the form "m * (p) / (q)" where p is a Laurent polynomial expanded with respect to the monomial basis and q is a polynomial written as a product of factors "(1-m)" where m is a multivariate monomial. Variables are "z1", ..., "zn" and exponentiation is written "z1**3", for example.
        """

        if not self:
            return 0
        else:
            ambdim=0
            for ii in self:
                ambdim=ii.ambient_dimension
                break
            PP = PolynomialRing(QQ,["z"+str(i) for i in range(ambdim)])
            FF = PP.fraction_field()
            z = FF.gens()
        def ratfun_cone(cone,fundamental_parallelepiped):
            d = cone.ambient_dimension
            V = cone.generators

            num = sum((prod([z[i]**t[i] for i in range(len(t))]) for t in fundamental_parallelepiped))
            den = prod([ 1-prod([ z[i]**c[i] for i in range(d) ]) for c in V])
            return num/den
        rational_functions = []
        for cone, multiplicity in self.items():
            pi = fundamental_parallelepipeds[cone]
            rational_functions.append( multiplicity * ratfun_cone(cone,pi) )
        if len(rational_functions) > 0:
            self._rational_function = sum(rational_functions)
        else:
            self._rational_function = 0
        print(self._rational_function)

        return PP(self._rational_function)
    


# Import time for timing
from time import *

def get_optimum(A,b,f,upper_bound,lower_bound=0):
    _optimization_bound = var("a")
    A = [f] + A
    b = [_optimization_bound] + b
    print("The optimization problem")
    print(A)
    print(b)
    lds = LinearDiophantineSystem(A, b, [0 for i in range(len(b)-1)]+[0], _optimization_bound )

    print("Computing cones")
    t1=time()
    cones = lds.symbolic_cones(non_iterations=1,logging=True)
    t2=time()
    print("Cones computation took: ", t2-t1, " secs for ", len(cones), " cones")
    print(cones)
    upper = upper_bound
    lower = lower_bound
    tmp = upper

    while True:
        cut_value = ceil((upper+lower)/2)
        print("Cut value: ", cut_value)
        if tmp==cut_value:
            if nsols!=0:
                return cut_value,rf.exponents()
            else:
                cut_value=cut_value-1
                nsols, rf = lds.get_for_cut(cut_value)
                return cut_value,rf.exponents()
        nsols, rf = lds.get_for_cut(cut_value)

        if nsols == 1:
            return cut_value,rf.exponents()

        if nsols == 0:
            upper=cut_value
        else:
            lower=cut_value

        tmp = cut_value
        print("For ", cut_value, " we have ", nsols, " solutions")
        print( rf)

A = [[-2,-1],[-1,-2]]
b = [-5,-5]
f = [1,1]
P= Polyhedron(ieqs=[ [-b[i]] + [ j for j in A[i] ] for i in range(len(b))]+[ [0] + [ 1 if j==i else 0 for j in range(len(A[0]))] for i in range(len(A[0]))])
P.show()
ta=time()
get_optimum(A,b,f,4)
tb=time()
print("It took only ", tb-ta, " seconds")