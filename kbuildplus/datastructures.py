import pdb
trace = pdb.set_trace
import z3
import pycudd
import vcommon as CM

import settings
mlog = CM.getLogger(__name__, settings.logger_level)

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


class Multiverse(list):
    def __init__(self, ls=[]):
        assert all(isinstance(cd, CondDef) for cd in ls), ls
        
        list.__init__(self, ls)

    def __str__(self, printCond=None):
        return "CondDefs([{}])".format(
            ', '.join([p.__str__(printCond) for p in self]))
    
    def dedup(self):
        uniqs = set(cd.mdef for cd in self)
        if len(uniqs) == len(self):
            return self

        cache = {}
        for cond, zcond, val in self:
            if val in cache:
                c, zc = cache[val]
                cache[val] = (c | cond, z3.Or(zc, zcond)) #disj
            else:
                cache[val] = (cond, zcond)

        mv = Multiverse([CondDef(c, zc, v)
                         for v, (c, zc)  in cache.iteritems()])
        assert mv
        return mv

class VarEntry(tuple):
    RECURSIVE = "RECURSIVE"
    SIMPLE = "SIMPLE"
    
    def __new__(cls, val, cond, zcond, flavor):
        return super(VarEntry, cls).__new__(cls, (val, cond, zcond, flavor))
    
    def __init__(self, val, cond, zcond, flavor):
        assert val is None or isinstance(val, str), val
        assert isinstance(cond, pycudd.DdNode), cond
        assert z3.is_expr(zcond), cond
        assert flavor in set({VarEntry.RECURSIVE, VarEntry.SIMPLE}), flavor

        self.val = val.strip() if isinstance(val, str) else val
        self.cond = cond
        self.zcond = z3.simplify(zcond)
        self.flavor = flavor

    def __str__(self, printCond=None):
        ss = [self.val, self.flavor]
        if printCond:
            ss.append(printCond(self.cond))
            
        ss.append(self.zcond)
            
        return "; ".join(map(str,ss))

    @property
    def condDef(self):
        return CondDef(self.cond, self.zcond, self.val)

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
        ss = [self.idx, self.zbdd]
        if printCond:
            ss.append(printCond(self.bdd))

        return ", ".join(map(str,ss))


class Results:
    def __init__(self):
        self.subdirs = set()
        self.compilation_units = set()
        self.library_units = set()
        self.composites = set()
        self.hostprog_units = set()
        self.hostprog_composites = set()
        self.unconfigurable_units = set()
        self.extra_targets = set()
        self.clean_files = set()
        self.c_file_targets = set()
        # self.unit_pcs = set()
        # self.subdir_pcs = set()
        self.presence_conditions = {}

    def __str__(self, details=False):
        f = lambda k, s: "{}: {}".format(k, ', '.join(s) if details else len(s))
        delim = '\n' if details else ', '
        ss = delim.join(f(k, s) for k, s in self.__dict__.iteritems() if s)
        if self.presence_conditions:
            ss += '\n{} presence conditions: \n{}'.format(len(self.presence_conditions), self.z3_str(self.presence_conditions))
        # if self.unit_pcs:
        #     ss += '\n{} unit pcs: \n{}'.format(len(self.unit_pcs), self.pc_str(self.unit_pcs))
        # if self.subdir_pcs:
        #     ss += '\n{} subdir pcs: \n{}'.format(len(self.subdir_pcs), self.pc_str(self.subdir_pcs))
        return ss
    
    def pc_str(self, s):
        return '\n'.join("{}. {}: {}, {}".format(i, v, f, z3.simplify(g))
                         for i, (v, f, g) in enumerate(s))
    
    def z3_str(self, s):
        return '\n'.join("{}: {}".format(i, z3.simplify(s[i]))
                         for i in s.keys())

        
        
