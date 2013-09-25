#############################################################################
#
# value.py
#
# description: a class to hold semantic objects, that is, values of
# interpreted constants, and values assigned by models
#
#
# Authors:
# Jeremy Avigad
#
#
##############################################################################


class Value(object):
    """The class of semantic values
    
    Arguments:
    - pyval: a python value
    - is_num: a boolean, indicates that pyval supports numeric operations
    - desc: a boole expression that, together with the pyval, gives a description
      of the object in question
    """

    def __init__(self, pyval=None, desc=None, is_num=False):
        """Creats the object
        """
        self.pyval = pyval
        self.desc = desc
        self.is_num = is_num
        
    # TODO: what should the string method do? For now, just take the Python
    # object
    def __str__(self):
        return str(self.pyval)
    
    def is_num(self):
        return self.is_num
    

