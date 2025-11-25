# Python clauses useful for easily calling pybatfish API
class Clause:
    def __init__(self,communities:list[str],prefixes:list[str]):
        self.communities = communities
        self.prefixes = prefixes

    def format(self) -> str:
        communityStrings = list(map(lambda c: f"comm = {c}",self.communities))
        prefixStrings = list(map(lambda p: f"prefix = {p}",self.prefixes))
        joined = ",".join(communityStrings+prefixStrings)
        return f"[{joined}]"

class LocationPropertyPair:
    # location should be either: ip -> ip for edge or ip for node (already formatted)
    # property should be a list of clauses
    def __init__(self,location:str,property:list[Clause]):
        self.location = location 
        self.property = property

    def formatProperty(self) -> str:
        return "".join(map(lambda c: c.format(),self.property))

class VerificationQuery:
    def __init__(self, target:LocationPropertyPair,assumptions:list[LocationPropertyPair]):
        self.target = target
        self.assumptions = assumptions

    def format(self) -> dict:
        result = { "target" : self.target.formatProperty(), "location" : self.target.location }
        result["assumption_locations"] = ",".join(map(lambda a: a.location,self.assumptions))
        result["assumptions"] = ",".join(map(lambda a: a.formatProperty(),self.assumptions))
        return result