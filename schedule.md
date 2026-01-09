---
title: "Schedule"
layout: splash
days:
  - 2026-01-06 00:00:00-08:00
  - 2026-01-08 00:00:00-08:00
  - 2026-01-13 00:00:00-08:00
  - 2026-01-15 00:00:00-08:00
  - 2026-01-20 00:00:00-08:00
  - 2026-01-22 00:00:00-08:00
  - 2026-01-27 00:00:00-08:00
  - 2026-01-29 00:00:00-08:00
  - 2026-02-03 00:00:00-08:00
  - 2026-02-05 00:00:00-08:00
  - 2026-02-10 00:00:00-08:00
  - 2026-02-12 00:00:00-08:00
  - 2026-02-17 00:00:00-08:00
  - 2026-02-19 00:00:00-08:00
  - 2026-02-24 00:00:00-08:00
  - 2026-02-26 00:00:00-08:00
  - 2026-03-03 00:00:00-08:00
  - 2026-03-05 00:00:00-08:00
  - 2026-03-10 00:00:00-07:00
  - 2026-03-12 00:00:00-07:00

holidays:
  - description: Martin Luther King Jr. Day
    hide_time: true
    date: 2026-01-19 00:00:00-08:00
    type: raw_event
    name: Holiday
    color: "#e9ffdb"
---

<style type="text/css">
span.discussion { color: #dc267f; font-weight: bold }
span.lecture { color: #fe6100; font-weight: bold }
span.noclass { background-color:rgb(234, 174, 184); font-weight: bold }
tr:nth-child(odd)   { background-color:#eee; }
tr:nth-child(even)    { background-color:#fff; }
tbody>tr>:nth-child(3) {min-width:5em;}
</style>

## Schedule of topics (subject to change!)
{% assign lec = 0 %}

| Date             | Topic                                          | Notes
|------------------|------------------------------------------------|------------------------------------------------------------------------------------------------------------
| {{page.days[lec] | date: '%a %-m/%-d/%y'}}  {% assign lec = lec | plus:1 %} | Course overview and basics of Coq    | [Course overview](course-overview.html); [Preface](slides/lf/Preface.html); [Basics](slides/lf/Basics.html)
| {{page.days[lec] | date: '%a %-m/%-d/%y'}}  {% assign lec = lec | plus:1 %} | Induction and datastructures         | [Induction](slides/lf/Induction.html)
| {{page.days[lec] | date: '%a %-m/%-d/%y'}}  {% assign lec = lec | plus:1 %} | continued                            | [Lists](slides/lf/Lists.html)
| {{page.days[lec] | date: '%a %-m/%-d/%y'}}  {% assign lec = lec | plus:1 %} | continued                            | 
| {{page.days[lec] | date: '%a %-m/%-d/%y'}}  {% assign lec = lec | plus:1 %} | | 
| {{page.days[lec] | date: '%a %-m/%-d/%y'}}  {% assign lec = lec | plus:1 %} | | 
| {{page.days[lec] | date: '%a %-m/%-d/%y'}}  {% assign lec = lec | plus:1 %} | Polymorphism, functions as data      | [Poly](slides/lf/Poly.html)
| {{page.days[lec] | date: '%a %-m/%-d/%y'}}  {% assign lec = lec | plus:1 %} | continued                            |
| {{page.days[lec] | date: '%a %-m/%-d/%y'}}  {% assign lec = lec | plus:1 %} | More Tactics                         | [Tactics](slides/lf/Tactics.html)
| {{page.days[lec] | date: '%a %-m/%-d/%y'}}  {% assign lec = lec | plus:1 %} | Logic in Coq                         | [Logic](slides/lf/Logic.html)
| {{page.days[lec] | date: '%a %-m/%-d/%y'}}  {% assign lec = lec | plus:1 %} | continued                            |
| {{page.days[lec] | date: '%a %-m/%-d/%y'}}  {% assign lec = lec | plus:1 %} | continued                            |
| {{page.days[lec] | date: '%a %-m/%-d/%y'}}  {% assign lec = lec | plus:1 %} | Inductively defined propositions     | [IndProd](slides/lf/IndProd.html); [ProofObjects](slides/lf/ProofObjects.html)                                    
| {{page.days[lec] | date: '%a %-m/%-d/%y'}}  {% assign lec = lec | plus:1 %} | continued                            |
| {{page.days[lec] | date: '%a %-m/%-d/%y'}}  {% assign lec = lec | plus:1 %} | Total and partial maps; IMP          | [Maps](slides/lf/Maps.html); [Imp](slides/lf/Imp.html); [ImpParser](slides/lf/ImpParser.html); [ImpCEvalFun](slides/lf/ImpCEvalFun.html)
| {{page.days[lec] | date: '%a %-m/%-d/%y'}}  {% assign lec = lec | plus:1 %} | IMP: modeling an imperative language |                                                                 
| {{page.days[lec] | date: '%a %-m/%-d/%y'}}  {% assign lec = lec | plus:1 %} | Program equivalence                  | [Equiv](slides/lf/Equiv.html)
| {{page.days[lec] | date: '%a %-m/%-d/%y'}}  {% assign lec = lec | plus:1 %} | Hoare Logic                          | [Hoare](slides/lf/Hoare.html); [Hoare2](slides/lf/Hoare2.html)
| {{page.days[lec] | date: '%a %-m/%-d/%y'}}  {% assign lec = lec | plus:1 %} |                                      |                                                                 
| {{page.days[lec] | date: '%a %-m/%-d/%y'}}  {% assign lec = lec | plus:1 %} |                                      |                                                                 
| {{page.days[lec] | date: '%a %-m/%-d/%y'}}  {% assign lec = lec | plus:1 %} |                                      |                                                                 
| {{page.days[lec] | date: '%a %-m/%-d/%y'}}  {% assign lec = lec | plus:1 %} |                                      |                                                                 
| {{page.days[lec] | date: '%a %-m/%-d/%y'}}  {% assign lec = lec | plus:1 %} |                                      |                                                                 
| {{page.days[lec] | date: '%a %-m/%-d/%y'}}  {% assign lec = lec | plus:1 %} |                                      |                                                                 
| {{page.days[lec] | date: '%a %-m/%-d/%y'}}  {% assign lec = lec | plus:1 %} |                                      |                                                                 
| {{page.days[lec] | date: '%a %-m/%-d/%y'}}  {% assign lec = lec | plus:1 %} |                                      |                                                                 
| {{page.days[lec] | date: '%a %-m/%-d/%y'}}  {% assign lec = lec | plus:1 %} |                                      |                                                                 
| {{page.days[lec] | date: '%a %-m/%-d/%y'}}  {% assign lec = lec | plus:1 %} |                                      |                                                                 
| {{page.days[lec] | date: '%a %-m/%-d/%y'}}  {% assign lec = lec | plus:1 %} |                                      |                                                                 
| {{page.days[lec] | date: '%a %-m/%-d/%y'}}  {% assign lec = lec | plus:1 %} |                                      |                                                                 
| {{page.days[lec] | date: '%a %-m/%-d/%y'}}  {% assign lec = lec | plus:1 %} |                                      |                                                                 
| {{page.days[lec] | date: '%a %-m/%-d/%y'}}  {% assign lec = lec | plus:1 %} |                                      |                                                                 
| {{page.days[lec] | date: '%a %-m/%-d/%y'}}  {% assign lec = lec | plus:1 %} |                                      |                                                                 
| {{page.days[lec] | date: '%a %-m/%-d/%y'}}  {% assign lec = lec | plus:1 %} |                                      |                                                                 
| {{page.days[lec] | date: '%a %-m/%-d/%y'}}  {% assign lec = lec | plus:1 %} |                                      |                                                                 
| {{page.days[lec] | date: '%a %-m/%-d/%y'}}  {% assign lec = lec | plus:1 %} |                                      |                                                                 
