# NFLPA Case Competition: Cumulative Workload Analysis

**2025-26 NFLPA Data Analytics Case Competition Submission**

This project was prepared for the [NFLPA Data Analytics Case Competition](https://nflpa.com/datacompetition), which challenges participants to examine how cumulative effects of workload throughout the season impact player performance, injury risk, earnings, or team wins and losses. The competition asks: *What 2-3 priorities should the NFLPA focus on to better advocate for the interests of players relating to cumulative workload?*

**Competition Details:**
- **Challenge**: Analyze cumulative workload effects and propose policy priorities for the NFLPA
- **Submission Requirements**: Executive summary (<1 page) + detailed write-up (≤2,000 words, ≤10 tables/visualizations)
- **Evaluation Criteria**: Rationale for cumulative effects evaluation, data validity and methods, feasibility of proposed approach from union and management perspectives
- **Competition Website**: [nflpa.com/datacompetition](https://nflpa.com/datacompetition)

---

Analysis of NFL scheduling patterns and their impact on player injuries, performance, and competitive fairness (2015-2024).

## Overview

This project examines how rest periods, schedule compression, and cumulative workload affect player health and competitive balance in the NFL. Using survival analysis, causal inference methods (differences-in-differences, marginal structural models), and Bayesian hierarchical modeling, we quantify the impact of Thursday Night Football, the 17-game season expansion, and rest differentials on injury risk.

## Key Findings

1. **Thursday Night Football**: Players with high short-rest exposure face 68% higher injury hazard. Optimizing TNF scheduling to occur only after bye weeks would prevent 8-9 injuries per season while preserving TV revenue.

2. **17-Game Season**: The schedule expansion increased late-season injury risk by 0.35 injuries per game, with effects accumulating over time. A second bye week would mitigate this impact.

3. **Rest Differentials**: 42.6% of games feature rest differentials exceeding 2 days, creating unfair competitive disadvantages. Capping rest differentials at ±2 days would improve competitive fairness and prevent ~2 injuries per season.

## Repository Structure

### Reports
- `Full Analysis.pdf` - Complete technical analysis (1,995 words)
- `Executive Summary.pdf` - High-level summary for stakeholders

### Analysis Scripts
- `nflpa_tnf_analysis_v2.R` - Primary frequentist analysis (survival models, DiD, MSM, counterfactuals)
- `nflpa_bayesian_analysis.R` - Bayesian multilevel models with posterior predictive checks

## Requirements

### R Packages
- `tidyverse` (dplyr, ggplot2, tidyr, etc.)
- `survival`, `survminer` - Survival analysis
- `brms`, `rstan` - Bayesian modeling
- `nflreadr`, `nflfastR` - NFL data
- `MASS`, `sandwich`, `lmtest` - Statistical modeling
- Additional packages as needed (see script imports)

## Usage

### Running the Analysis

1. **Frequentist Analysis**:
```r
source("nflpa_tnf_analysis_v2.R")
```
Generates all plots and prints key findings to console.

2. **Bayesian Analysis**:
```r
source("nflpa_bayesian_analysis.R")
```
Fits Bayesian multilevel models and generates posterior distributions.

### Data Sources

The analysis uses publicly available NFL data from:
- `nflreadr` - Official injury reports, schedules
- `nflfastR` - Play-by-play data, EPA metrics

Data is automatically downloaded when scripts are run (requires internet connection).

## Methodology

- **Survival Analysis**: Cox proportional hazards models for time-to-injury (descriptive/observational)
- **Differences-in-Differences**: 17-game season expansion as natural experiment (causal)
- **Marginal Structural Models**: Inverse probability weighting for time-varying confounding (causal)
- **Bayesian Hierarchical Models**: Multilevel models with team/season random effects
- **Counterfactual Simulations**: Policy impact estimation

All models use clustered standard errors at the team level. See `Full Analysis.pdf` for complete methodological details.

## Policy Recommendations

1. **Optimize TNF Scheduling**: Schedule all Thursday games only after bye weeks (10+ days rest)
2. **Add Second Bye Week**: Provide mid-season recovery to reduce cumulative fatigue
3. **Cap Rest Differentials**: Limit rest imbalances to ±2 days in schedule generator

All policies can be implemented as schedule generator constraints without structural CBA changes.

## License

This analysis was prepared for the NFLPA Case Competition. Data sources are publicly available through `nflreadr` and `nflfastR`.
