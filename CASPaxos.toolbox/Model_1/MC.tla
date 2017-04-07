---- MODULE MC ----
EXTENDS CASPaxos, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
a1, a2, a3
----

\* MV CONSTANT definitions Acceptors
const_14915459371072000 == 
{a1, a2, a3}
----

\* CONSTANT definitions @modelParameterConstants:0Values
const_14915459371173000 == 
{0, 1, 2, 3}
----

\* CONSTANT definitions @modelParameterConstants:2Mutator(b, v)
const_14915459371284000(b, v) == 
(1 + b*v) % 4
----

\* CONSTANT definition @modelParameterDefinitions:0
def_ov_14915459371405000 ==
0..3
----
\* SPECIFICATION definition @modelBehaviorSpec:0
spec_14915459371516000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_14915459371617000 ==
DesiredProperties
----
=============================================================================
\* Modification History
\* Created Fri Apr 07 02:18:57 EDT 2017 by tschottdorf
