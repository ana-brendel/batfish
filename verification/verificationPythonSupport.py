# Python clauses useful for easily calling pybatfish API
class Clause:
    def __init__(self,communities:list[str]=[],prefixes:list[str]=[]):
        self.communities = communities
        self.prefixes = prefixes

    def format(self) -> str:
        communityStrings = list(map(lambda c: f"comm = {c}",self.communities))
        prefixStrings = list(map(lambda p: f"prefix = {p}",self.prefixes))
        joined = " & ".join(communityStrings+prefixStrings)
        return f"[{joined}]"
    
class Property:
    def __init__(self,clauses:list[Clause]):
        self.clauses = clauses

    def formatProperty(self) -> str:
        return "".join(map(lambda c: c.format(),self.clauses))

class LocationPropertyPair:
    # location should be either: ip -> ip for edge or ip for node (already formatted)
    # property should be a list of clauses
    def __init__(self,location:str,property:list[Clause]):
        self.location = location 
        self.property = property

    def formatProperty(self) -> str:
        return "".join(map(lambda c: c.format(),self.property))

class VerificationQuery:
    def __init__(self, target:LocationPropertyPair,assumptions:list[LocationPropertyPair],default:Property=Property([]),refine:bool=False):
        self.target = target
        self.assumptions = assumptions
        self.default = default
        self.refine = refine

    def refines(self):
        return self.refine
    
    def defaultAssumption(self):
        return self.default.formatProperty()
    
    def targetProperty(self):
        return self.target.formatProperty()
    
    def targetLocation(self):
        return self.target.location
    
    def assumptionLocations(self):
        return ",".join(map(lambda a: a.location,self.assumptions))
    
    def assumptionProperties(self):
        return ",".join(map(lambda a: a.formatProperty(),self.assumptions))