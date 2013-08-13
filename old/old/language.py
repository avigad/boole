################################################################################
#
# language.py
#
# description: the language class provides a dictionary from type and expressions
# to python objects; the types and expressions are keyed by their names.
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
# Exceptions associated with Languages
#
################################################################################

class AlreadyDef(Exception):
    """Raised if trying to re-define a type
    """
    
    def __init__(self, name):
        """
        
        Arguments:
        - `name`: The name of the already defined type
        """
        mess = "{0} is already defined.".format(name)
        Exception.__init__(self, mess)
        self.name = name

        
################################################################################
#
# Language: the language class provides a dictionary from type and expressions
# to python objects; the types and expressions are keyed by their names.
#
################################################################################


class Language():
    """A dictionary of symbols (basic types and constants) that have been
    declared
    """
    
    def __init__(self):
        self.type_dict = {}
        self.const_dict = {}
        
    def add_type(self, type):
        """Adds the name of the type to the language
        """
        # TODO: add a warning if redefining a type in
        # built_in_language
        if type.name in self.type_dict:
            raise AlreadyDef(type.name)
        else:
            self.type_dict[type.name] = type
        
    def add_const(self, const):
        """Adds the name of the constant to the language
        """
        self.const_dict[const.name] = const
        
    def has_type(self, name):
        return name in self.type_dict.keys()
    
    def has_const(self, name):
        return name in self.const_dict.keys()
    
    def get_type(self, name):
        return self.type_dict[name]
    
    def get_const(self, name):
        return self.const_dict[name]
    
    def reset(self):
        self.type_dict = {}
        self.const_dict = {}
        
    def show(self):
        for type_name in self.type_dict.keys():
            print 'Basic types: \'' + type_name + '\''
        for const_name in self.const_dict.keys():
            print 'Constants: \'' + const_name + '\'',
            const = self.const_dict[const_name]
            try:
                print 'of type \'' + str(const.etype()) + '\'',
            except TypeError:
                print 'of unknown type',
            if const.attributes.keys():
                print ' ', str(const.attributes)
            else:
                print

                
# some initial languages

built_in_language = Language()    # for built-in symbols
global_language = Language()      # a default global language


# a language that doesn't store anything

class NullLanguage(Language):
    
    def add_type(self, t):
        pass
    
    def add_const(self, c):
        pass
    
null_language = NullLanguage()


# Language operations

_default_language = global_language
        
def set_default_language(language = global_language):
    global _default_language
    
    _default_language = language
    
def get_default_language():
    return _default_language

def get_language(language):
    
    if language == None:
        return _default_language
    else:
        return language

def clear_default_language():
    global _default_language

    _default_language = Language()
