congruence.vo congruence.glob congruence.v.beautified congruence.required_vo: congruence.v safety.vo
congruence.vio: congruence.v safety.vio
congruence.vos congruence.vok congruence.required_vos: congruence.v safety.vos
fairness.vo fairness.glob fairness.v.beautified fairness.required_vo: fairness.v congruence.vo
fairness.vio: fairness.v congruence.vio
fairness.vos fairness.vok fairness.required_vos: fairness.v congruence.vos
leads_to.vo leads_to.glob leads_to.v.beautified leads_to.required_vo: leads_to.v ltl.vo
leads_to.vio: leads_to.v ltl.vio
leads_to.vos leads_to.vok leads_to.required_vos: leads_to.v ltl.vos
liveness.vo liveness.glob liveness.v.beautified liveness.required_vo: liveness.v ltl.vo
liveness.vio: liveness.v ltl.vio
liveness.vos liveness.vok liveness.required_vos: liveness.v ltl.vos
ltl.vo ltl.glob ltl.v.beautified ltl.required_vo: ltl.v 
ltl.vio: ltl.v 
ltl.vos ltl.vok ltl.required_vos: ltl.v 
safety.vo safety.glob safety.v.beautified safety.required_vo: safety.v ltl.vo
safety.vio: safety.v ltl.vio
safety.vos safety.vok safety.required_vos: safety.v ltl.vos
termination.vo termination.glob termination.v.beautified termination.required_vo: termination.v ltl.vo
termination.vio: termination.v ltl.vio
termination.vos termination.vok termination.required_vos: termination.v ltl.vos
