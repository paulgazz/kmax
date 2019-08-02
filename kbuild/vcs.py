#!/usr/bin/env python
import pdb
import re
import argparse
import os.path
import tempfile
import sys
from collections import defaultdict

from pymake import parser, parserdata, data
import pycudd
import _pycudd

import z3
import vcommon as CM
import settings

mlog = None

trace = pdb.set_trace

matchUnexpandedVars = re.compile(r'.*\$\(.*\).*')
def containUnexpanded(s):
    assert s is None or (isinstance(s, str) and s), s
    return s is not None and matchUnexpandedVars.match(s)

def myjoin(l, delim=""):
    return delim.join(e for e in l if e)
    
#symbolic operations
def conj(a, b):
    assert isinstance(a, pycudd.DdNode), a
    assert isinstance(b, pycudd.DdNode), b    
    return a & b

def disj(a, b):
    assert isinstance(a, pycudd.DdNode), a
    assert isinstance(b, pycudd.DdNode), b    
    return a | b

def neg(c):
    assert isinstance(c, pycudd.DdNode), c    
    return ~c

        
class BoolVar(tuple):
    def __new__(cls, bdd, zbdd, idx):
        assert isinstance(bdd, pycudd.DdNode), bdd
        assert idx >= 0, idx
        
        return super(BoolVar, cls).__new__(cls, (bdd, zbdd, idx))
    
    def __init__(self, bdd, zbdd, idx):
        assert isinstance(bdd, pycudd.DdNode), bdd
        assert z3.is_expr(zbdd), zbdd
        assert idx >= 0, idx
        
        self.bdd = bdd
        self.zbdd = zbdd
        self.idx = idx

    def __str__(self, printCond=None):
        ss = [self.idx, zbdd]
        if printCond:
            ss.append(printCond(self.bdd))

        return ", ".join(map(str,ss))
        
                                    
class VarProp(tuple):
    RECURSE = "RECURSE"
    SIMPLE = "SIMPLE"
    
    def __new__(cls, val, cond, zcond, flavor):
        return super(VarProp, cls).__new__(cls, (val, cond, flavor))
    
    def __init__(self, val, cond, zcond, flavor):
        assert val is None or (isinstance(val, str) and val), val
        assert isinstance(cond, pycudd.DdNode), cond
        assert z3.is_expr(zcond), cond
        
        assert flavor in set({VarProp.RECURSE, VarProp.SIMPLE}), flavor

        self.val = val.strip() if isinstance(val, str) else val
        self.cond = cond
        self.zcond = z3.simplify(zcond)
        self.flavor = flavor

    def __str__(self, printCond=None):
        ss = [self.val, self.flavor]
        if printCond:
            ss.append(printCond(self.cond))
            ss.append(self.zcond)
            
        return ", ".join(map(str,ss))

class CondDef(tuple):
    def __new__(cls, cond, zcond, mdef):
        return super(CondDef, cls).__new__(cls, (cond, zcond, mdef))
    
    def __init__(self, cond, zcond, mdef):
        assert isinstance(cond, pycudd.DdNode), cond
        assert z3.is_expr(zcond)
        
        assert mdef is None or isinstance(mdef, str), mdef  #CONFIG_A, 'y', 'm'
        self.cond = cond
        self.zcond = zcond
        self.mdef = mdef

    def __str__(self, printCond=None):
        if not printCond:
            return "{}".format(self.mdef)
        else:
            return "({}, {}, {})".format(printCond(self.cond), self.zcond, self.mdef)

    @classmethod
    def mkOne(cls, name, cond, zcond):
        assert isinstance(name, str) and name, name
        assert isinstance(cond, pycudd.DdNode), cond
        assert z3.is_expr(zcond)
        
        return cls(cond, zcond, name)

class CondDefs(list):
    def __init__(self, ls=[]):
        list.__init__(self, ls)

    def append(self, cd):
        assert isinstance(cd, CondDef), cd

        super(CondDefs, self).append(cd)
        
    def __str__(self, printCond=None):
        return "CondDefs([{}])".format(
            ', '.join([p.__str__(printCond) for p in self]))

    @classmethod
    def mkOne(cls, name, cond, zcond):
        assert isinstance(name, str) and name, name
        assert isinstance(cond, pycudd.DdNode), cond
        assert z3.is_expr(zcond)

        return cls([CondDef.mkOne(name, cond, zcond)])


class ZSolver:
    zT = z3.BoolVal(True)
    zF = z3.BoolVal(False)        
    
    def __init__(self):
        self.solver = z3.Solver()

    def zcheck(self, f):
        self.solver.push()
        self.solver.add(f)
        ret = self.solver.check()
        self.solver.pop()
        return ret

    
    
class KBuild:
    def __init__(self):
        self.mgr = pycudd.DdManager()
        self.mgr.SetDefault()

        self.zsolver = ZSolver()
        
        self.T = self.mgr.One()
        self.F = self.mgr.Zero()

        defVarProp = lambda: [VarProp(None, self.T, ZSolver.zT, VarProp.RECURSE)]
        self.kvars = defaultdict(defVarProp) #var -> [varprop]
        defBoolVar = lambda: BoolVar(self.mgr.IthVar(len(self.bvars)),
                                     z3.Bool("b{}".format(len(self.bvars))),
                                     len(self.bvars))
        self.bvars = defaultdict(defBoolVar) #boolean var -> bdd var number
        self.undefvars = set()

        self.tokenPC = {}
        self.unitPC = {}
        self.subdirPC = {}
        self.compositePC = {}

    def doStmts(self, stmts, cond, zcond):
        assert isinstance(stmts, parserdata.StatementList), stmts
        assert isinstance(cond, pycudd.DdNode), cond
        assert z3.is_expr(zcond), zcond
        
        for s in stmts:
            if isinstance(s, parserdata.SetVariable):
                self.doSetVariable(s, cond, zcond)
            elif isinstance(s, parserdata.ConditionBlock):
                self.doConditionBlock(s, cond, zcond)
            else:
                raise NotImplementedError

    def doSetVariable(self, setvar, cond, zcond):
        assert isinstance(setvar, parserdata.SetVariable), setvar
        assert isinstance(cond, pycudd.DdNode), cond
        assert z3.is_expr(zcond), zcond
        
        def updatePCs(name, mycond, myzcond):
            if name.endswith("-y") or name.endswith("-m"):
                for v in val.split():  #zatm.o uPD98402.o
                    if v.endswith(".o") or v.endswith("/"):
                        if v not in self.tokenPC:
                            self.tokenPC[v] = (self.T, ZSolver.zT)

                        c, zc = self.tokenPC[v]
                        self.tokenPC[v] = (conj(c, mycond),
                                           z3.simplify(z3.And(zc, myzcond)))

                        if name in set(["obj-y", "obj-m"]):
                            if v.endswith('.o'):
                                self.unitPC[v] = self.tokenPC[v]
                            elif v.endswith("/"):
                                self.subdirPC[v] = self.tokenPC[v]

        #bj-y := fork.o
        name = self.expand(setvar.vnameexp)                
        token = setvar.token
        val = setvar.value
        #print 'doSetVariable', name, token, val
        
        if isinstance(name, str):
            self.addVarProp(name, token, val, cond, zcond)
            updatePCs(name, cond, zcond)
            
        else:
            assert isinstance(name, CondDefs), name
            for cd in name:
                cond_ = conj(cd.cond, cond)
                zcond_ = z3.And(cd.zcond, zcond)
                #print cd.mdef, token, val, self.bdd2str(cond_)
                self.addVarProp(cd.mdef, token, val, cond_, zcond_)
                updatePCs(cd.mdef, cond_, zcond_)

    def doElem(self, elem, isfun):
        #elem: VariableRef<tests/kbuild/paper_example:2:6>(Exp<None>('CONFIG_A'))
        assert isinstance(elem, (str, parserdata.functions.VariableRef)), elem
        assert isinstance(isfun, bool), isfun

        if isinstance(elem, str):
            return elem
        elif isfun:
            return self.doFun(elem)
        else:
            raise NotImplementedError


    def doFun(self, fun):
        assert isinstance(fun, parserdata.functions.VariableRef), fun

        if isinstance(fun, parserdata.functions.VariableRef):
            name = CondDefs.mkOne(self.expand(fun.vname), self.T, ZSolver.zT)  #repack_singleton
            #trace()
            expandednames = CondDefs()
            for cd in name:
                expandedname = self.doVariableRef(cd.mdef)
                for cd_ in expandedname:
                    cd = CondDef(conj(cd.cond, cd_.cond),
                                 z3.And(cd.zcond, cd_.zcond),
                                 cd_.mdef)
                    expandednames.append(cd)

            #print expandedname.__str__(self.bdd2str)
            assert isinstance(expandednames, CondDefs), expandednames
            return expandednames
        else:
            raise NotImplementedError
                    
    def doVariableRef(self, name):  #TODO: unclear, seems to add all possible option
        assert isinstance(name, str) and name, name
        
        #elif isBooleanConfig(name) or not hasConfig() and name.startswith("CONFIG_"):    #Todo
        if name.startswith("CONFIG_"):
            by = self.bvars[name + "=y"]
            bm = self.bvars[name + "=m"]
            
            equalsy, equalszy = by.bdd, by.zbdd
            equalsm, equalszm = bm.bdd, bm.zbdd
            defined, zdefined = self.getDefined(name, True)

            #todo: optimization
            definedy = conj(defined, conj(equalsy, neg(equalsm)))
            definedzy = z3.And(zdefined, z3.And(equalszy, z3.Not(equalszm)))
            
            definedm = conj(defined, conj(equalsm, neg(equalsy)))
            definedzm = z3.And(zdefined, z3.And(equalszm, z3.Not(equalszy)))

            undefined, zundefined = self.getDefined(name, False)
            
            myundefined = disj(undefined, conj(neg(definedy), neg(definedm)))
            myzundefined = z3.Or(zundefined, z3.And(z3.Not(definedzy), z3.Not(definedzm)))
            cds = [CondDef(definedy, definedzy, 'y'), CondDef(definedm, definedzm, 'm'),
                   CondDef(undefined, myzundefined, None)]
            cds = CondDefs(cds)            
            return cds
        else:
            if name in self.undefvars:
                raise NotImplementederror
            
                cds = [CondDef(pv.cond, pv.val) for pv in self.kvars[name]]
                return CondDefs(cds)
            
            elif name not in self.kvars:  #TODO: did not include the isNonebooleanConfig
                # Leave undefined variables unexpanded

                mlog.warn("Undef var expansion {}".format(name))
                
                self.undefvars.add(name)
                self.kvars[name] = [
                    VarProp("$({})".format(name), self.T, ZSolver.zT, VarProp.RECURSE)]


                cds = [CondDef(vp.cond,  vp.zcond, vp.val) for vp in self.kvars[name]]
                cds = CondDefs(cds)
                return cds

            else:
                exps = CondDefs()
                for vp in self.kvars[name]:
                    if vp.val:
                        exps.extend(self.expand2(vp.val, vp.cond))
                    else:
                        exps.append(CondDef(vp.cond, vp.val))
                return exps
                    
    def doConditionBlock(self, block, cond, zcond):
        assert isinstance(block, parserdata.ConditionBlock), block
        assert block and len(block) <= 2, block
        assert isinstance(cond, pycudd.DdNode), cond
        assert z3.is_expr(zcond), zcond
        
        hasElse = len(block) == 2

        bcond, stmts = block[0]
        firstCond, elseCond = self.getConds(cond, zcond, bcond, stmts)

        if not firstCond:
            print("could not get if branch cond")
            exit(1)
        self.doStmts(stmts, firstCond)

        if hasElse:
            _, stmts = block[1]
            self.doStmts(stmts, elseCond)
        
    #Utils
    def addVarProp(self, name, token, val, cond, zcond):
        assert isinstance(name, str), name
        assert isinstance(token, str), token
        assert isinstance(val, str), val
        assert isinstance(cond, pycudd.DdNode), cond
        assert z3.is_expr(zcond), zcond

        mlog.debug("{}: {} {} {} ({})"
                   .format(CM.whoami(), name, token, val, zcond ))
        
        negCond = lambda vpCond: conj(vpCond, neg(cond))
        negzCond = lambda vpzCond: z3.And(vpzCond, z3.Not(zcond))
        
        negVpCond = lambda vpCond: conj(neg(vpCond), cond)

        # Update all existing definitions' presence conditions        
        updatePC = lambda name: [
            VarProp(vp.val,
                    negCond(vp.cond),
                    negzCond(vp.zcond),
                    vp.flavor)
            for vp in self.kvars[name]]
        
        
        if token == "=":            
            # tvn: TODO: Paul uses get_var_equiv_set

            self.kvars[name] = updatePC(name)

            # Add complete definition to variable (needed to find variable
            # expansions at use-time)
            self.kvars[name].append(VarProp(val, cond, zcond, VarProp.RECURSE))
            
        elif token == ":=":
            
            # tvn: TODO: Paul uses get_var_equiv_set
            # tvn: create SIMPLE prop

            
            # Simply-expanded self.kvars are expanded at define-time

            # Update all existing definitions' presence conditions
            # AFTER getting the new definition, since the new
            # definition might refer to itself as in
            # linux-3.0.0/crypto/Makefile
            oldVars = updatePC(name)
            # Expand and flatten self.kvars in the definition and add the
            # resulting definitions.
            newDefs = self.expand2(val, cond, zcond)
            newVars = [VarProp(v, c, zc, VarProp.SIMPLE) for c, zc, v in newDefs]
            self.kvars[name] = oldVars + newVars
            
        elif token == "+=":
            #tvn: create RECURSE prop

            
            newVars = []
            for vp in self.kvars[name]:
                newCond = conj(vp.cond, cond)
                newzCond = z3.simplify(z3.And(vp.zcond, zcond))

                if newCond == self.F:
                    assert newzCond == ZSolver.zF, (newCond, newzCond)

                if newCond == self.T:
                    assert newzCond == ZSolver.zT, (newCond, newzCond)
                
                if newzCond == ZSolver.zF:
                    raise NotImplementedError
                    # Make two separate definitions.  One updates the
                    # existing definition's presence_condition.  The
                    # other creates a new definition
                    newVars.append(
                        VarProp(vp.val, negCond(vp.cond), cond), vp.flavor)
                    newCond = negVpCond(vp.cond)
                    
                    if vp.flavor == VarProp.SIMPLE:
                        newDefs = self.expand2(val, newCond)
                        newVars_ = [VarProp(v,c, vp.flavor) for c,v in newDefs]
                        newVars.extend(newVars_)
                        
                    elif vp.flavor == VarProp.RECURSE:
                        newVars.append(VarProp(val, newCond, vp.RECURSE))

                    else:
                        assert False
                else:  #newCond != F
                    aval = myjoin([vp.val, val], delim=" ")
                    if vp.flavor == VarProp.SIMPLE:
                        raise NotImplementedError
                    
                        newDefs = self.expand2(aval, newCond)
                        newVars_ = [VarProp(v,c, vp.flavor) for c,v in newDefs]
                        newVars.extend(newVars_)
                        
                    else:
                        assert vp.flavor == VarProp.RECURSE, vp.flavor
                        newVars.append(VarProp(aval, newCond, newzCond, vp.flavor))

                        
                        
            self.kvars[name] = newVars
        else:
            raise NotImplementedError(token)

        #oldlen = len(self.kvars[name])
        #self.kvars[name] = [vp for vp in self.kvars[name] if vp.cond != self.F]
        tmp = []
        for entry in self.kvars[name]:
            ret = self.zsolver.zcheck(entry.zcond)
            if ret != z3.unsat:
                assert entry.cond != self.F
                tmp.append(entry)

        self.kvars[name] = tmp

    def repack(self, exp): #done
        assert isinstance(exp, (str, CondDefs)), exp
        return CondDefs([CondDef(self.T, ZSolver.zT, exp)]) if isinstance(exp, str) else exp

    def hoist(self, exp):
        assert isinstance(exp, list) and exp, exp
        assert all(isinstance(e, (str, CondDefs)) for e in exp), exp

        #trace()
        hoisted = [(self.T, ZSolver.zT, [])]
        for e in exp:
            if isinstance(e, CondDefs):
                newlist = []
                for cd in e:
                    for c, zc, ds in hoisted:
                        newc = conj(c, cd.cond)
                        newzc = z3.And(zc, cd.zcond)
                        newds = ds + [cd.mdef]
                        newlist.append((newc, newzc, newds))
                hoisted = newlist
            else:
                assert isinstance(e, str), e
                for _, _, ds in hoisted:
                    ds.append(e)
                    
        rs = [(c, zc, myjoin(ds)) for c, zc, ds in hoisted]

        #remove dups
        d = {}
        for c, zc, v in rs:
            if v not in d:
                d[v] = (c, zc)
            else:
                d[v] = (disj(d[v], c), z3.Or(d[v][1], zd))
                
        if len(d) < len(rs):
            rs = [(c, zc, v) for v, (c, zc) in d.iteritems()]
            
        rs = CondDefs([CondDef(c, zc, None if not v else v) for c, zc, v in rs])
        return rs
        
    def expand(self, exp):
        """
        """
        assert isinstance(exp, (data.StringExpansion, data.Expansion)), exp
        
        if isinstance(exp, data.StringExpansion):
            rs = exp.s
        else:
            #trace()
            rs = [self.doElem(elem, isfun) for elem, isfun in exp]
            rs = self.hoist(rs)
        assert isinstance(rs, str) or isinstance(rs, CondDefs), rs
        return rs

    def expand2(self, val, cond, zcond):
        assert isinstance(val, str), val
        assert isinstance(cond, pycudd.DdNode), cond
        assert z3.is_expr(zcond), zcond
        
        d = parser.Data.fromstring(val, None)
        e, t, o = parser.parsemakesyntax(d, 0, (), parser.iterdata)
        assert t is None and o is None, t

        exp = self.expand(e)
        if isinstance(exp, str):
            return CondDefs([CondDef(cond, zcond, exp)])
        else:
            return exp
        
    def getConds(self, cond, zcond, bcond, stmts):
        assert isinstance(cond, pycudd.DdNode), cond
        assert z3.is_expr(zcond), zcond        
        assert isinstance(bcond,
                          (parserdata.EqCondition,parserdata.IfdefCondition)), bcond
        assert isinstance(stmts, parserdata.StatementList), stmts

        firstCond = None
        if isinstance(bcond, parserdata.IfdefCondition):
            raise NotImplementedError
            exp = self.expand(bcond.exp)
            if isinstance(exp, str):
                firstCond = self.getDefined(exp, bcond.expected)
            else:
                assert False
            elseCond = neg(firstCond)
            
        elif isinstance(bcond, parserdata.EqCondition):  #ifeq ($(CONFIG_A),y)

            exp1 = self.repack(self.expand(bcond.exp1))
            exp2 = self.repack(self.expand(bcond.exp2))

            hoistedCond = self.F
            hoistedzCond = ZSolver.zF
            hoistedElse = self.F
            hoistedzElse = ZSolver.zF

            print len(exp1), len(exp2)
            print exp1
            print exp2
            for cd1 in exp1:
                for cd2 in exp2:
                    print cd1.__str__(self.bdd2str)
                    print cd2.__str__(self.bdd2str)
                    
                    assert isinstance(cd1, CondDef)
                    assert isinstance(cd2, CondDef)

                    tcond = conj(cd1.cond, cd2.cond)
                    tzcond = z3.simplify(z3.And(cd1.zcond, cd2.zcond))

                    if tcond != self.F:
                        assert not z3.is_false(tzcond)
                    
                    if tcond != self.F and (cd1.mdef == cd2.mdef) == bcond.expected:
                        print 'gh0'
                        hoistedCond = disj(hoistedCond, tcond)
                        hoistedzCond = z3.Or(hoistedzCond, tzcond)
                    elif tcond != self.F:
                        print 'gh1'
                        hoistedElse = disj(hoistedElse, tcond)
                        hoistedzElse = z3.Or(hoistedzElse, tzcond)
                    else:
                        assert False

                    if containUnexpanded(cd1.mdef) or containUnexpanded(cd2.mdef):
                        assert False

                firstCond = conj(cond, hoistedCond)
                firstzCond = z3.And(zcond, hoistedzCond)                
                elseCond = conj(cond, hoistedElse)
                elsezCond = z3.And(zcond, hoistedzElse)
            
        else:
            # print exp1.__str__(self.bdd2str)
            # print exp2.__str__(self.bdd2str)  
            assert False

        return firstCond, firstzCond, elseCond, elsezCond

    def getDefined(self, var, expected): #done
        assert isinstance(var, str) and var, var
        assert isinstance(expected, bool), expected

        varname = "defined({})" .format(var)
        if expected:
            return self.bvars[varname].bdd, self.bvars[varname].zbdd
        else:
            return neg(self.bvars[varname].bdd), z3.Not(self.bvars[varname].zbdd)

    def printSymbTable(self, printCond=None):
        for name in self.kvars:
            if 'obj-' == name: continue  #inf loop on drivers/atm/Makefile
            print "var: {}".format(name)

            print '\n'.join("{}. {}".format(i, v.__str__(printCond))
                            for i,v in enumerate(self.kvars[name]))
            print '---------'

        
    def bdd2cnf(self, condition):
        assert isinstance(condition, pycudd.DdNode), condition        
        """Converts the expression to conjunctive normal form

        @returns a list of terms, represented as lists of factors"""
        stdout = os.dup(1)
        temp_fd, temp_filename = tempfile.mkstemp()
        sys.stdout.flush()
        os.dup2(temp_fd, 1)
        condition.PrintMinterm()
        sys.stdout.flush()
        os.dup2(stdout, 1)
        os.close(stdout)
        os.lseek(temp_fd, 0, os.SEEK_SET)
        with os.fdopen(temp_fd) as f:
            expression = []
            for line in filter(lambda l: len(l) > 0, (l.rstrip() for l in f.readlines())):
                minterm = list(line)
                term = []
                for name in self.bvars:
                    value = minterm[self.bvars[name].idx]
                    if value == '1':
                        term.append(name)
                    elif value == '0':
                        term.append("!" + name)
                    elif value == '-':
                        pass
                    else: fatal("Unknown setting for variable in minterm", minterm)
                expression.append(term)
            return expression
        print("Could not open temp file containing minterms", temp_file)
        exit(1)
        
    def bdd2str(self, cond):
        """Converts the expression to a string"""
        assert isinstance(cond, pycudd.DdNode), cond

        if cond == self.T:
            return "1"
        elif cond == self.F:
            return "0"

        def _join(l, delim):
            if not l:
                return None
            elif len(l) == 1:
                return l[0]
            else:
                return '({})'.format(delim.join(map(str, l)))


        exprs = self.bdd2cnf(cond)
        exprs = [_join(l, ' && ') for l in exprs]
        exprs = [e for e in exprs if e]
        exprs = _join(exprs, ' || ')
        return exprs if exprs else "1"


    def splitDefs(self, mvar):
        assert isinstance(mvar, str), mvar
        #print mvar, self.kvars[mvar]
        
        vals = []
        for vp in self.kvars[mvar]:
            if not vp.val: continue
            #print vp.val
            cds = self.repack(self.expand2(vp.val, vp.cond, vp.zcond))
            for cd in cds:
                if not cd.mdef: continue
                svals = cd.mdef.split()
                vals.extend(svals)

        return vals
    
    def collect(self, dname, mvars, compileUnits, subdirs, composites):

        assert os.path.isdir(dname), dname
        assert isinstance(mvars, set) and mvars, mvars
        assert isinstance(compileUnits, set), units
        assert isinstance(subdirs, set), subdirs
        assert isinstance(composites, set), composites

        done = set()
        notdone = set(mvars)
        while notdone:
            mvar = notdone.pop()
            done.add(mvar)

            vals = self.splitDefs(mvar)
            for uname in vals:
                unameFull = os.path.normpath(os.path.join(dname, uname))
                if uname.endswith('.o') and unameFull not in compileUnits:
                    uname_ = uname[:-2]
                    composite1 = uname_ + "-objs"
                    composite2 = uname_ + "-y"
                    if composite1 in self.kvars or composite2 in self.kvars:
                        # scripts/Makefile.build use the -objs and -y
                        # suffix to define composites $($(subst
                        # $(obj)/,,$(@:.o=-objs))) $($(subst
                        # $(obj)/,,$(@:.o=-y)))), $^)
                        if composite1 not in done and composite2 not in done:
                            composites.add(unameFull)
                            notdone.add(composite1)
                            notdone.add(composite2)

                        unameFull_ = unameFull[:-2]
                        cfile = unameFull_ + ".c"
                        sfile = unameFull_ + ".S"
                        if os.path.isfile(cfile) or os.path.isfile(sfile):
                            compileUnits.add(unameFull)
                    else:
                        compileUnits.add(unameFull)
                        
                elif uname.endswith("/"):
                    # scripts/Makefile.lib takes anything that
                    # ends in a forward slash as a subdir
                    # $(patsubst %/,%,$(filter %/, $(obj-y)))
                    print 'add to', uname
                    subdirs.add(uname)
                                        

def extract(makefile, compileUnits, composites, unitPC, subdirPC):
    assert os.path.isfile(makefile) or os.path.isdir(makefile), makefile
    assert isinstance(compileUnits, set), compileUnits
    assert isinstance(composites, set), composites
    assert isinstance(unitPC, set), unitPC
    assert isinstance(subdirPC, set), subdirPC
    
    #pdb.set_trace()
    
    if not os.path.isfile(makefile):
        assert isinstance(os.path.isdir(makefile)), makefile
        
        mdir = makefile
        makefile = os.path.join(mdir, "Kbuild")
        if not os.path.isfile(makefile):
            makefile = os.path.join(mdir, "Makefile")
            assert makefile, makefile

    mlog.info("Analyzing '{}'".format(makefile))
    
    dname = os.path.dirname(makefile)
    makefile = open(makefile, "rU")
    contents = makefile.read()
    makefile.close()

    stmts = parser.parsestring(contents, makefile.name)
    kbuild = KBuild()
    kbuild.doStmts(stmts, kbuild.T, ZSolver.zT)

    #collect results
    subdirs = set()
    kbuild.collect(dname,
                   set([ "obj-y" ]),  #, "obj-m"   #TODO: auto detect these
                   compileUnits,
                   subdirs,
                   composites)

    def _pcs(d, s):
        for name, (cond, zcond) in d.iteritems():
            s.add((os.path.normpath(os.path.join(dname, name)),
                   kbuild.bdd2str(cond),
                   zcond))

    _pcs(kbuild.unitPC, unitPC)
    _pcs(kbuild.subdirPC, subdirPC)
        
    #print results
    kbuild.printSymbTable(printCond=kbuild.bdd2str)
    
    #clean up 
    _pycudd.delete_DdManager(kbuild.mgr)
    return subdirs

if __name__ == '__main__':
    
    aparser = argparse.ArgumentParser("find interactions from Kbuild Makefile")
    ag = aparser.add_argument
    
    ag('makefile',
       type=str,
       help="""the name of a Kbuild Makefile or subdir""")
    
    #0 Error #1 Warn #2 Info #3 Debug #4 Detail
    ag("--logger_level", "-logger_level", "-log", "--log",
       help="set logger info",
       type=int, 
       choices=range(5),
       default = 4)    
    
    ag('-t', '--table',
       action="store_true",
       help="""show symbol table entries""")
    
    ag('-r', '--recursive',
       action="store_true",
       help="""recursively enter subdirectories""")
    
    args = aparser.parse_args()
    
    if args.logger_level != settings.logger_level and 0 <= args.logger_level <= 4:
        settings.logger_level = args.logger_level
    settings.logger_level = CM.getLogLevel(settings.logger_level)
    mlog = CM.getLogger(__name__, settings.logger_level)
    
    if __debug__:
        mlog.warn("DEBUG MODE ON. Can be slow! (Use python -O ... for optimization)")
    
    subdirectories = set([args.makefile])
    compileUnits = set()
    composites = set()
    unitPC = set()
    subdirPC = set()
    while subdirectories:
        mdir = subdirectories.pop()
        ndir = extract(
            mdir,
            compileUnits,
            composites,
            unitPC,
            subdirPC)
        subdirectories.update(ndir)
        if not args.recursive:
            break
        
        if not args.recursive:
            break


    if compileUnits:
        print "{} compile units: {}".format(
            len(compileUnits), ', '.join(map(str,compileUnits)))

    for v, c, zc in unitPC:
        print v, c, zc
    for v, c, zc in subdirPC:
        print v, c, zc
