import read, copy
from util import *
from logical_classes import *

verbose = 0

class KnowledgeBase(object):
    def __init__(self, facts=[], rules=[]):
        self.facts = facts
        self.rules = rules
        self.ie = InferenceEngine()

    def __repr__(self):
        return 'KnowledgeBase({!r}, {!r})'.format(self.facts, self.rules)

    def __str__(self):
        string = "Knowledge Base: \n"
        string += "\n".join((str(fact) for fact in self.facts)) + "\n"
        string += "\n".join((str(rule) for rule in self.rules))
        return string

    def _get_fact(self, fact):
        """INTERNAL USE ONLY
        Get the fact in the KB that is the same as the fact argument

        Args:
            fact (Fact): Fact we're searching for

        Returns:
            Fact: matching fact
        """
        for kbfact in self.facts:
            if fact == kbfact:
                return kbfact

    def _get_rule(self, rule):
        """INTERNAL USE ONLY
        Get the rule in the KB that is the same as the rule argument

        Args:
            rule (Rule): Rule we're searching for

        Returns:
            Rule: matching rule
        """
        for kbrule in self.rules:
            if rule == kbrule:
                return kbrule

    def kb_add(self, fact_rule):
        """Add a fact or rule to the KB
        Args:
            fact_rule (Fact|Rule) - the fact or rule to be added
        Returns:
            None
        """
        printv("Adding {!r}", 1, verbose, [fact_rule])
        if isinstance(fact_rule, Fact):
            if fact_rule not in self.facts:
                self.facts.append(fact_rule)
                for rule in self.rules:
                    self.ie.fc_infer(fact_rule, rule, self)
            else:
                if fact_rule.supported_by:
                    ind = self.facts.index(fact_rule)
                    for f in fact_rule.supported_by:
                        self.facts[ind].supported_by.append(f)
                else:
                    ind = self.facts.index(fact_rule)
                    self.facts[ind].asserted = True
        elif isinstance(fact_rule, Rule):
            if fact_rule not in self.rules:
                self.rules.append(fact_rule)
                for fact in self.facts:
                    self.ie.fc_infer(fact, fact_rule, self)
            else:
                if fact_rule.supported_by:
                    ind = self.rules.index(fact_rule)
                    for f in fact_rule.supported_by:
                        self.rules[ind].supported_by.append(f)
                else:
                    ind = self.rules.index(fact_rule)
                    self.rules[ind].asserted = True

    def kb_assert(self, fact_rule):
        """Assert a fact or rule into the KB

        Args:
            fact_rule (Fact or Rule): Fact or Rule we're asserting
        """
        printv("Asserting {!r}", 0, verbose, [fact_rule])
        self.kb_add(fact_rule)

    def kb_ask(self, fact):
        """Ask if a fact is in the KB

        Args:
            fact (Fact) - Statement to be asked (will be converted into a Fact)

        Returns:
            listof Bindings|False - list of Bindings if result found, False otherwise
        """
        print("Asking {!r}".format(fact))
        if factq(fact):
            f = Fact(fact.statement)
            bindings_lst = ListOfBindings()
            # ask matched facts
            for fact in self.facts:
                binding = match(f.statement, fact.statement)
                if binding:
                    bindings_lst.add_bindings(binding, [fact])

            return bindings_lst if bindings_lst.list_of_bindings else []

        else:
            print("Invalid ask:", fact.statement)
            return []

    def kb_retract(self, fact_or_rule):
        """Retract a fact from the KB

        Args:
            fact (Fact) - Fact to be retracted

        Returns:
            None
        """
        printv("Retracting {!r}", 0, verbose, [fact_or_rule])
        ####################################################
        if isinstance(fact_or_rule, Fact) and fact_or_rule in self.facts: #if input is a Fact that exists, continue
            if fact_or_rule.asserted: #if Fact is asserted, continue
                ind = self.facts.index(fact_or_rule) #find fact inserted in database
                #if fact is supported, leave it alone, but make it no longer asserted
                if len(self.facts[ind].supported_by) > 0:
                    self.facts[ind].asserted = False
                    return
                #if fact is not supported, remove it
                else:
                    # for each fact that it supports...
                    for supported_fact in self.facts[ind].supports_facts:
                        #find supported fact in database
                        ind_sf = self.facts.index(supported_fact)
                        KB_sf = self.facts[ind_sf]
                        for index, fact_rule_list in enumerate(KB_sf.supported_by):
                            if fact_rule_list[0] == fact_or_rule:
                                KB_sf.supported_by.pop(index)
                        self.kb_retract_recursive(KB_sf)
                    # for each rule that it supports
                    for supported_rule in self.facts[ind].supports_rules:
                        # find supported rule in database
                        ind_sr = self.rules.index(supported_rule)
                        KB_sr = self.rules[ind_sr]
                        for index, fact_rule_list in enumerate(KB_sr.supported_by):
                            if fact_rule_list[0] == fact_or_rule:
                                KB_sr.supported_by.pop(index)
                        self.kb_retract_recursive(KB_sr)
                    # remove the fact from the kb
                    del self.facts[ind]


    def kb_retract_recursive(self, fact_or_rule):
        """Helper function for retracting a fact from the KB

        Args:
            fact_or_rule is a (Fact) or a (Rule)"""

        # for removing inferred facts that are no longer supported
        if isinstance(fact_or_rule, Fact) and fact_or_rule in self.facts:
            if not fact_or_rule.asserted:
                # if fact is not asserted and supported by nothing, it's removed
                if len(fact_or_rule.supported_by) == 0:
                    ind = self.facts.index(fact_or_rule)
                    del self.facts[ind]
                    # handle facts it was supporting
                    for supported_fact in fact_or_rule.supports_facts:
                        # find supported fact in database
                        ind_sf = self.facts.index(supported_fact)
                        KB_sf = self.facts[ind_sf]
                        for index, fact_rule_list in enumerate(KB_sf.supported_by):
                            if fact_rule_list[0] == fact_or_rule:
                                KB_sf.supported_by.pop(index)
                        self.kb_retract_recursive(KB_sf)
                    # handle rules it was supporting
                    for supported_rule in fact_or_rule.supports_rules:
                        # find supported rule in database
                        ind_sr = self.rules.index(supported_rule)
                        KB_sr = self.rules[ind_sr]
                        for index, fact_rule_list in enumerate(KB_sr.supported_by):
                            if fact_rule_list[0] == fact_or_rule:
                                KB_sr.supported_by.pop(index)
                        self.kb_retract_recursive(KB_sr)

        # for inferred rules that are no longer supported
        elif isinstance(fact_or_rule, Rule) and fact_or_rule in self.rules:
            if not fact_or_rule.asserted:
                # if fact is not asserted and supported by nothing, it's removed
                if len(fact_or_rule.supported_by) == 0:
                    ind = self.rules.index(fact_or_rule)
                    del self.rules[ind]
                    # handle facts it was supporting
                    for supported_fact in fact_or_rule.supports_facts:
                        # find supported fact in database
                        ind_sf = self.facts.index(supported_fact)
                        KB_sf = self.facts[ind_sf]
                        for index, fact_rule_list in enumerate(KB_sf.supported_by):
                            if fact_rule_list[1] == fact_or_rule:
                                KB_sf.supported_by.pop(index)
                        self.kb_retract_recursive(KB_sf)
                    # handle rules it was supporting
                    for supported_rule in fact_or_rule.supports_rules:
                        # find supported rule in database
                        ind_sr = self.rules.index(supported_rule)
                        KB_sr = self.rules[ind_sr]
                        for index, fact_rule_list in enumerate(KB_sr.supported_by):
                            if fact_rule_list[1] == fact_or_rule:
                                KB_sr.supported_by.pop(index)
                        self.kb_retract_recursive(KB_sr)

class InferenceEngine(object):
    def fc_infer(self, fact, rule, kb):
        """Forward-chaining to infer new facts and rules

        Args:
            fact (Fact) - A fact from the KnowledgeBase
            rule (Rule) - A rule from the KnowledgeBase
            kb (KnowledgeBase) - A KnowledgeBase

        Returns:
            Nothing            
        """
        printv('Attempting to infer from {!r} and {!r} => {!r}', 1, verbose,
            [fact.statement, rule.lhs, rule.rhs])
        ####################################################
        binding = match(fact.statement, rule.lhs[0]) # False if there is a binding
        if binding:
            if len(rule.lhs) == 1:
                # then, the right hand side is instantiated and this is a fact for each binding
                # supported by/from/etc
                new_statement = instantiate(rule.rhs, binding)
                new_fact = Fact(new_statement, [[fact, rule]])
                fact.supports_facts.append(new_fact)
                rule.supports_facts.append(new_fact)
                kb.kb_add(new_fact)
            else:
                # then, there is a new rule, for the rest of the lhs -> rhs
                # but only with that binding, for each binding
                # supported by/from/etc
                lhs_statements = [] # rule[0] for Rule(rule, supported_by)
                for lhs_rule in rule.lhs[1:]: # sublist containing all but first element
                    new_lsh_statement = instantiate(lhs_rule, binding)
                    lhs_statements.append(new_lsh_statement)
                rhs_statement = instantiate(rule.rhs, binding)
                new_rule = Rule([lhs_statements,rhs_statement],[[fact, rule]])
                fact.supports_rules.append(new_rule)
                rule.supports_rules.append(new_rule)
                kb.kb_add(new_rule)




