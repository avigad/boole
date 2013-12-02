import boole.elaboration.unif as unif
import boole.core.tactics as tactics
import boole.core.conv as conv
from boole.semantics.value import eval_expr
from boole.elaboration.prelude import *

import sys

if 'sage' in sys.argv:
    config.in_sage()

try:
    import sage
    config.in_sage
except Exception:
    pass
