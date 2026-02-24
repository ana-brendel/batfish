# COPIED FROM PYBATFISH REPO

# Importing required libraries, setting up logging, and loading questions
import logging
import random  # noqa: F401
from typing import List, Optional  # noqa: F401

import pandas as pd
from IPython.display import display
from pandas.io.formats.style import Styler

from pybatfish.client.session import Session  # noqa: F401

# noinspection PyUnresolvedReferences
from pybatfish.datamodel import Edge, Interface  # noqa: F401
from pybatfish.datamodel.answer import TableAnswer
from pybatfish.datamodel.flow import HeaderConstraints, PathConstraints  # noqa: F401
from pybatfish.datamodel.route import BgpRoute  # noqa: F401
from pybatfish.util import get_html

# Configure all pybatfish loggers to use WARN level
logging.getLogger("pybatfish").setLevel(logging.WARN)

pd.set_option("display.max_colwidth", None)
pd.set_option("display.max_columns", None)
# Prevent rendering text between '$' as MathJax expressions
pd.set_option("display.html.use_mathjax", False)

# UUID for CSS styles used by pandas styler.
# Keeps our notebook HTML deterministic when displaying dataframes
_STYLE_UUID = "pybfstyle"


class MyStyler(Styler):
    """A custom styler for displaying DataFrames in HTML"""

    def __repr__(self):
        return repr(self.data)


def show(df):
    """
    Displays a dataframe as HTML table.

    Replaces newlines and double-spaces in the input with HTML markup, and
    left-aligns the text.
    """
    if isinstance(df, TableAnswer):
        df = df.frame()

    # workaround for Pandas bug in Python 2.7 for empty frames
    if not isinstance(df, pd.DataFrame) or df.size == 0:
        display(df)
        return
    display(
        MyStyler(df)
        .set_uuid(_STYLE_UUID)
        .format(get_html)
        .set_properties(**{"text-align": "left", "vertical-align": "top"})
    )

from verificationPythonSupport import LocationPropertyPair,LivenessQuery,SafetyQuery,Clause,Property

# Help functions to run tests and examples easier
def create(networkName:str,snapshotName:str,snapshotPath:str):
    '''Creates a batfish session for the snapshot located at `snapshotPath` and is given the provided `networkName` and `snapshotName`.'''
    bf = Session(host="localhost")
    bf.set_network(networkName)
    bf.init_snapshot(snapshotPath, name=snapshotName, overwrite=True)
    return bf

# This function is what includes the call to the pybatfish safety property verification question
def runSafetyVerificationQuestion(bf,show_all:bool,query:SafetyQuery):
    '''Returns the result of making the provided VerificationQuery `query` using the provided batfish session `bf`. The provided
    `show_all` flag indicates if all locations results should be displayed or just the most relevant ones.'''
    if query == None:
        return bf.q.safety().answer().frame()
    assumptionLocations = query.assumptionLocations()
    defaultAssumption = query.defaultAssumption()
    if assumptionLocations == "":
        if defaultAssumption == "":
            result = bf.q.safety(
                target=query.targetProperty(),
                location=query.targetLocation(),
                show_all=show_all,
                refine=query.refines()).answer()
        else:
            result = bf.q.safety(
                target=query.targetProperty(),
                location=query.targetLocation(),
                default_assumption = defaultAssumption,
                show_all=show_all,
                refine=query.refines()).answer()
    elif defaultAssumption == "":
        result = bf.q.safety(
            target=query.targetProperty(),
            location=query.targetLocation(),
            assumption_locations=assumptionLocations,
            assumptions=query.assumptionProperties(),
            show_all=show_all,
            refine=query.refines()).answer()
    else:
        result = bf.q.safety(
            target=query.targetProperty(),
            location=query.targetLocation(),
            assumption_locations=assumptionLocations,
            assumptions=query.assumptionProperties(),
            default_assumption = defaultAssumption,
            show_all=show_all,
            refine=query.refines()).answer()
    return result.frame()

# This function is what includes the call to the pybatfish liveness property verification question
def runLivenessVerificationQuestion(bf,query:LivenessQuery):
    '''Returns the result of making the provided VerificationQuery `query` using the provided batfish session `bf`. The provided
    `show_all` flag indicates if all locations results should be displayed or just the most relevant ones.'''
    if query == None:
        return bf.q.liveness().answer().frame()
    assumptionLocations = query.assumptionLocations()
    defaultAssumption = query.defaultAssumption()
    ingressEdge = query.getIngress()

    if ingressEdge == None:
        if assumptionLocations == None:
            if defaultAssumption == None:
                result = bf.q.liveness(
                    prefix=query.getPrefix(),
                    target=query.targetProperty(),
                    location=query.targetLocation()).answer()
            else:
                result = bf.q.liveness(
                    prefix=query.getPrefix(),
                    target=query.targetProperty(),
                    location=query.targetLocation(),
                    default_assumption = defaultAssumption).answer()
        elif defaultAssumption == None:
            result = bf.q.liveness(
                prefix=query.getPrefix(),
                target=query.targetProperty(),
                location=query.targetLocation(),
                assumption_locations=assumptionLocations,
                assumptions=query.assumptionProperties()).answer()
        else:
            result = bf.q.liveness(
                prefix=query.getPrefix(),
                target=query.targetProperty(),
                location=query.targetLocation(),
                assumption_locations=assumptionLocations,
                assumptions=query.assumptionProperties(),
                default_assumption = defaultAssumption).answer()
    else: 
        if assumptionLocations == None:
            if defaultAssumption == None:
                result = bf.q.liveness(
                    prefix=query.getPrefix(),
                    target=query.targetProperty(),
                    location=query.targetLocation(),
                    ingress=ingressEdge).answer()
            else:
                result = bf.q.liveness(
                    prefix=query.getPrefix(),
                    target=query.targetProperty(),
                    location=query.targetLocation(),
                    default_assumption = defaultAssumption,
                    ingress=ingressEdge).answer()
        elif defaultAssumption == None:
            result = bf.q.liveness(
                prefix=query.getPrefix(),
                target=query.targetProperty(),
                location=query.targetLocation(),
                assumption_locations=assumptionLocations,
                assumptions=query.assumptionProperties(),
                ingress=ingressEdge).answer()
        else:
            result = bf.q.liveness(
                prefix=query.getPrefix(),
                target=query.targetProperty(),
                location=query.targetLocation(),
                assumption_locations=assumptionLocations,
                assumptions=query.assumptionProperties(),
                default_assumption = defaultAssumption,
                ingress=ingressEdge).answer()
    return result.frame()

def runAndDisplay(networkName:str,snapshotName:str,snapshotPath:str,query,show_all=False):
    '''Runs and displays the result of running the VerificationQuery `query` on the snapshot located at `snapshotPath`. The optional `show_all`
    flag is passed to the query with a default value of False.'''
    bf = create(networkName,snapshotName,snapshotPath)
    if query == None:
        return bf.q.safety().answer().frame()
    elif type(query) == LivenessQuery:
        verificationResult = runLivenessVerificationQuestion(bf,query)
        show(verificationResult)
    elif type(query) == SafetyQuery:
        verificationResult = runSafetyVerificationQuestion(bf,show_all,query)
        show(verificationResult)

def runAndGet(networkName:str,snapshotName:str,snapshotPath:str,query,show_all=False):
    '''Runs and displays the result of running the VerificationQuery `query` on the snapshot located at `snapshotPath`. The optional `show_all`
    flag is passed to the query with a default value of False.'''
    bf = create(networkName,snapshotName,snapshotPath)
    if type(query) == LivenessQuery:
        return runLivenessVerificationQuestion(bf,query)
    elif type(query) == SafetyQuery:
        return runSafetyVerificationQuestion(bf,show_all,query)