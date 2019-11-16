import pdb
trace = pdb.set_trace
import z3
import kmax.vcommon as CM

import kmax.settings
mlog = CM.getLogger(__name__, kmax.settings.logger_level)

class CondDef(tuple):
    def __new__(cls, cond, zcond, mdef):
        return super(CondDef, cls).__new__(cls, (cond, zcond, mdef))
    
    def __init__(self, cond, zcond, mdef):
        assert z3.is_expr(zcond)
        
        assert mdef is None or isinstance(mdef, str), mdef  #CONFIG_A, 'y', 'm'
        self.cond = None
        self.zcond = zcond
        self.mdef = mdef

    def __str__(self, printCond=None):
        if not printCond:
            return "{}".format(self.mdef)
        else:
            return "({}, {})".format(self.zcond, self.mdef)


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
                cache[val] = (None, z3.Or(zc, zcond)) #disj
            else:
                cache[val] = (None, zcond)

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
        assert z3.is_expr(zcond), zcond
        assert flavor in set({VarEntry.RECURSIVE, VarEntry.SIMPLE}), flavor

        self.val = val.strip() if isinstance(val, str) else val
        self.cond = None
        self.zcond = z3.simplify(zcond)
        self.flavor = flavor

    def __str__(self, printCond=None):
        ss = [self.val, self.flavor]
            
        ss.append(self.zcond)
            
        return "; ".join(map(str,ss))

    @property
    def condDef(self):
        return CondDef(self.cond, self.zcond, self.val)

class BoolVar(tuple):
    def __new__(cls, bdd, zbdd, idx):
        assert idx >= 0, idx
        
        return super(BoolVar, cls).__new__(cls, (bdd, zbdd, idx))
    
    def __init__(self, bdd, zbdd, idx):
        assert z3.is_expr(zbdd), zbdd
        assert idx >= 0, idx
        
        self.bdd = None
        self.zbdd = zbdd
        self.idx = idx

    def __str__(self, printCond=None):
        ss = [self.idx, self.zbdd]
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

    def split_nested(self, s):
        # assume we've come in with "CONFIG_A)", i.e., no beginning
        # top-level lparen, but the matching rparen for it, because we
        # split on it in to_exp_step
        depth = 1
        operands = []
        operand = ""
        for c in s:
            if c=='(':
                depth += 1
                
            if c==')':
                depth -= 1

            if c==',' and depth==1 or c==')' and depth==0:
                operands.append(operand)
                # print operand
                operand = ""
            else:
                operand += c
        assert depth == 0  # we started without the top-level lparen, but with the top-level rparen, so we started on depth 1 and should exit on depth 0
        return operands
    
    def to_exp_step(self, s):
        # print s
        if s.startswith("And") or s.startswith("Or") or s.startswith("Not"):
            (opname, operands) = s.split('(', 1)
            operands = self.split_nested(operands)
            operands = [ self.to_exp_step(operand) for operand in operands ]
            # print opname, operands
            new_s = ""
            if opname=="And":
                new_s = "(" + " && ".join(operands) + ")"
            elif opname=="Or":
                new_s = "(" + " || ".join(operands) + ")"
            elif opname=="Not":
                assert len(operands) == 1
                new_s = "(! " + operands[0] + ")"
            # print "new_s", new_s
            return new_s
        if s=="True":
            return "1"
        else:
            return s
    
    def to_exp(self, s):
        s = str(s).replace('\n', '').replace(' ', '')
        
        return self.to_exp_step(s)

    def get_line_format(self, filename):
        if filename.endswith("/"):
            line_format = "subdir_pc {} {}"
        else:
            line_format = "unit_pc {} {}"

        return line_format
    
    def z3_str(self, path_conds):
        # print self.to_exp("And(CONFIG_RMMOD, Not(CONFIG_MODPROBE_SMALL))")
        # exit(1)
        # result = '\n'.join("unit_pc {} {}".format(i, self.to_exp(z3.simplify(s[i]))) + "\nunit_pc {} {}".format(i, z3.simplify(s[i]))
        #                  for i in s.keys())

        # # separate paths into files and subdirs, which end in forward slash
        # file_pcs = { path : cond for path, cond in path_conds.iteritems() if not path.endswith("/") }
        # subdir_pcs = { path : cond for path, cond in path_conds.iteritems() if path.endswith("/") }

        # # find full presence conditions for each file and conjoining the presence conditions for each path
        # full_pcs = {}

        # for path, cond in file_pcs.iteritems():
        #     subpath, basename = path.rsplit('/', 1)
        #     elems = subpath.rsplit('/')
        #     for i in reversed(range(0, 7)):
        #         subsubpath = '/'.join(elems[:-i])
        #         if len(subsubpath) == 0: subsubpath = "/"
        #         print subsubpath, subsubpath in subdir_pcs
        #         if subsubpath in subdir_pcs: print subsubpath, subdir_pcs[subsubpath]
        
        result = '\n'.join(self.get_line_format(filename).format(filename, self.to_exp(z3.simplify(path_conds[filename])))
                         for filename in path_conds.keys())
        return result
