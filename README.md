# RefinementOfVotingRules

Using Isabelle Monadic Refinement to generate performant code of voting rules.

The voting rules are originally specified in the Isabelle Framework for Verified Construction of Fair Voting rules (VCFVR) (https://github.com/VeriVote/verifiedVotingRuleConstruction).

## Goals

In the afforementioned frameworks, Isabelles' code generation is used to provide verified executable code.
In this project, the Isabelle refinement framework is used to improve the performance of the resulting code with respect to execution times. 

## Dependencies

This project depends on a fork from VCFVR (https://github.com/SpringVaS/verifiedVotingRuleConstruction). This dependency can be prebuild as described in its ROOT file. 

This project should build by running 
  `isabelle build -d $PATH_TO$/verifiedVotingRuleConstruction/theories/ -b -P "output" -D `pwd` `
