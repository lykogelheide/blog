# This simulation is based on a paper by [Blackwell and Glynn]
# (https://www.cambridge.org/core/journals/american-political-science-review/
# article/abs/how-to-make-causal-inferences-with-timeseries-crosssectional-data-
# under-selection-on-observables/498BE04E5AF9802EC4D33DD7A4016584). 
# You can find the Dataverse and replication files [here]
# (https://dataverse.harvard.edu/dataset.xhtml?persistentId=doi:10.7910/DVN/SFBX6Z).

library(plm)
library(sandwich)
library(lmtest)
library(RColorBrewer)
library(tidyverse)
library(parallel)
library(geepack)
library(ggplot2)
library(patchwork) 

#----- Initialize Simulation Parameters
inv.logit <- boot::inv.logit
set.seed(1337)
sig    <- 0.1
gamma1 <- c(0.5, 0)
gamma2 <- c(0.5, -0.5)
alpha1 <- c(-2.5, 1.5)
alpha2 <- c(-2.5, 1.5, -1)
mu1.1 <- 0.1
mu2.11 <- -0.25
mu2.01 <- -0.15
eta <- 0 #causal effect of x on z

gamma_list <- list(
  gamma1 = c(0.5, 0),
  gamma2 = c(0.5, -0.5)
)

eta_list <- list(
  eta0  = 0,
  eta03 = 0.3
)

n_sims <- 1000

sim_params <- list(
  sig = sig,
  gamma1 = gamma1,
  gamma2 = gamma2,
  alpha1 = alpha1,
  alpha2 = alpha2,
  mu1.1 = mu1.1,
  mu2.11 = mu2.11,
  mu2.01 = mu2.01,
  eta = eta_list,
  n_sims = n_sims
)
saveRDS(sim_params, file = "MSM/results/sim_params.rds")
#----- Generate Data
#--- Helper Functions
pan_lag <- function(x, ind, length = 1) {
  lag_one <- function(w) {
    adds <- rep(NA, times = length)
    drops <- seq(length(w), length(w) - (length - 1), by = -1)
    return(c(adds, w[-drops]))
  }
  unlist(tapply(x, ind, lag_one))
}

pan_prod <- function(x, ind) {
  unlist(tapply(x, ind, function(x) {
    xt <- x
    xt[!is.na(xt)] <- cumprod(na.omit(x))
    return(xt)
  }))
}

#--- DGP-Function
tscs.sim <- function(N = 100, T = 5, gamma, eta) {
  # yAB represents each of the 4 potential outcomes. A represents current lagged 
  # treatment status, B represents current treatment status 
  # (1 = treated, 0 = untreated)
  # Create placeholder matrices for potential outcomes
  y11 <- y10 <- y01 <- y00 <- matrix(NA, nrow = N, ncol = T)
  # Create placeholder matrices for variables
  z <- x <- y <- matrix(NA, nrow = N, ncol = T)
  # Unobserved heterogeneity 
  u <- rnorm(N, 0, sig)
  
  # confounder
  z[,1] <- 1.7 * u + rnorm(N, -0.4, sig)
  # prob of binary treatment
  p.x <- inv.logit(cbind(1, z[,1]) %*% alpha1)
  # binatry treatment indicator
  x[,1] <- rbinom(N, size = 1, prob = p.x)
  
  
  # baseline level depending on unobserved heterogeneity 
  eps1 <-  0.8 + 0.9 * u
  # baseline level + noise
  y00[,1] <- eps1 + eta * z[,1] + rnorm(N, 0, sig)
  # treated at t = 1: add contemporaneous treatment effect (CET)
  y01[,1] <- eps1 + mu2.01 + eta * z[,1] + rnorm(N, 0, sig)
  # lagged treatment (not there yet) - only baseline
  # treatment and lagged treatment
  y10[,1] <- y00[,1]
  y11[,1] <- y00[,1]
  # outcome
  y[,1] <- y01[,1] * x[,1] + y00[,1] * (1 - x[,1])
  
  # Create later time-period data based on previous time-period values
  for (t in 2:T) {
    # Baseline level + noise
    eps1 <-  0.8 + 0.9 * u
    e11 <- rnorm(N, 0, sig)
    e10 <- rnorm(N, 0, sig)
    e01 <- rnorm(N, 0, sig)
    e00 <- rnorm(N, 0, sig)
    
    # Potential outcomes for covariate z
    z1 <- gamma[1] + gamma[2] + 1.7 * u + rnorm(N, 0, sig)
    z0 <- gamma[1] + 1.7 * u + rnorm(N, 0, sig)
    # Actual z (covariate) depends on actual outcome
    z[,t] <- x[,t-1] * z1 + (1 - x[,t-1]) * z0
    
    # Potential outcomes for outcome
    # baseline level + lagged effect + current effect + noise
    y11[,t] <- eps1 + mu1.1 + mu2.11 + eta * z[,t] + e11
    # baseline level + lagged effect + noise
    y10[,t] <- eps1 + mu1.1          + eta * z[,t] + e10
    # baseline level + current effect + noise
    y01[,t] <- eps1 + mu2.01         + eta * z[,t] + e01
    # baseline level + noise
    y00[,t] <- eps1                  + eta * z[,t] + e00
    
    # prob of x (treatment) depends on time-varying covariate + lagged outcome + coefficient vector alpha2
    p.x <- cbind(1, z[,t], y[,t-1]) %*% alpha2 + rnorm(N, 0, 1)
    x[,t] <- 1 * (p.x > 0) # latent variable probit
    # baseline y00 + lagged treatment (x[,t-1] == 1) alone 
    y[,t] <- y00[,t] + x[,t-1] * (y10[,t] - y00[,t]) + 
      # + current treatment (no prev. but now treatment)
      x[,t] * (y01[,t] - y00[,t]) +
      # + interaction term when both treatments are active
      x[,t-1] * x[,t] * ((y11[,t] - y01[,t]) - (y10[,t] - y00[,t]))
  }
  
  ii <- rep(1:N, each = T)
  tt <- rep(1:T, times = N)
  uu <- rep(u, each = T)
  # actual/observed variables
  y.vec <- c(t(y))
  x.vec <- c(t(x))
  z.vec <- c(t(z))
  # potential outcomes
  y10.vec <- c(t(y10))
  y00.vec <- c(t(y00))
  y11.vec <- c(t(y11))
  y01.vec <- c(t(y01))
  
  pan_dat <- data.frame(ii = ii, tt = tt, y = y.vec, x = x.vec, z = z.vec,
                        y00 = y00.vec, y10 = y10.vec, y01 = y01.vec,
                        y11 = y11.vec, u = uu)
  
  #Create j-lagged variables
  pan_dat$ly  <- pan_lag(pan_dat$y, pan_dat$ii, 1)
  pan_dat$l2y <- pan_lag(pan_dat$y, pan_dat$ii, 2)
  pan_dat$l3y <- pan_lag(pan_dat$y, pan_dat$ii, 3)
  pan_dat$lx  <- pan_lag(pan_dat$x, pan_dat$ii, 1)
  pan_dat$l2x <- pan_lag(pan_dat$x, pan_dat$ii, 2)
  pan_dat$l3x <- pan_lag(pan_dat$x, pan_dat$ii, 3)
  pan_dat$lz  <- pan_lag(pan_dat$z, pan_dat$ii, 1)
  pan_dat$l2z <- pan_lag(pan_dat$z, pan_dat$ii, 2)
  pan_dat$l3z <- pan_lag(pan_dat$z, pan_dat$ii, 3)
  
  # Create a cumulative prior treatment exposure variable
  pan_dat$cumx  <- unlist(tapply(pan_dat$x, pan_dat$ii, cumsum)) - pan_dat$x
  pan_dat$lcumx <- pan_lag(pan_dat$cumx, pan_dat$ii, 2)  # lagged cum. exposure
  
  return(pan_dat)
  
}

#----- Run Statistical Models
#--- ADL (autoregressive distributed lag) models
adl_lagged <- function(mod) {
  coef(mod)["lx"] + coef(mod)["ly"] * coef(mod)["x"]
}

run_simulation <- function(N = 100, T = 5, gamma, eta) {
  # Generate data
  pan_dat <- tscs.sim(N = N, T = T, gamma = gamma, eta = eta)
  
  # True effects
  true_lagged <- pan_dat %>%
    filter(tt > 2) %>%
    summarise(ate = mean(y10 - y00)) %>%
    pull(ate)
  
  true_current <- pan_dat %>%
    filter(tt > 2) %>%
    summarise(ate = mean(y11 - y10)) %>%
    pull(ate)
  
  # Add weights to pan_dat
  ps_mod1 <- glm(x ~ ly + z + lx, data = pan_dat, na.action = na.exclude,
                 family = binomial(link = 'logit'))
  num_mod1 <- glm(x ~ lx, data = pan_dat, na.action = na.exclude,
                  family = binomial(link = "logit"))
  denom_scores1 <- fitted(ps_mod1) * pan_dat$x + 
    (1 - fitted(ps_mod1)) * (1 - pan_dat$x)
  num_scores1   <- fitted(num_mod1) * pan_dat$x + 
    (1 - fitted(num_mod1)) * (1 - pan_dat$x)
  ws1 <- num_scores1 / denom_scores1
  
  ps_mod2 <- glm(x ~ ly + z + lx + l2y + lz + l2x, data = pan_dat, 
                 na.action = na.exclude, family = binomial(link = 'logit'))
  num_mod2 <- glm(x ~ lx + l2x, data = pan_dat, 
                  na.action = na.exclude, family = binomial(link = "logit"))
  denom_scores2 <- fitted(ps_mod2) * pan_dat$x + 
    (1 - fitted(ps_mod2)) * (1 - pan_dat$x)
  num_scores2   <- fitted(num_mod2) * pan_dat$x + 
    (1 - fitted(num_mod2)) * (1 - pan_dat$x)
  ws2 <- num_scores2 / denom_scores2
  
  # Cumulative exposure propensity score
  ps_mod3 <- glm(x ~ ly + z + lx + lcumx, data = pan_dat, 
                 na.action = na.exclude, family = binomial(link = 'logit'))
  num_mod3 <- glm(x ~ lx + lcumx, data = pan_dat, 
                  na.action = na.exclude, family = binomial(link = "logit"))
  denom_scores3 <- fitted(ps_mod3) * pan_dat$x + 
    (1 - fitted(ps_mod3)) * (1 - pan_dat$x)
  num_scores3   <- fitted(num_mod3) * pan_dat$x + 
    (1 - fitted(num_mod3)) * (1 - pan_dat$x)
  ws3 <- num_scores3 / denom_scores3
  
  # Truncated weights
  lower1 <- quantile(ws1, probs = 0.05, na.rm = TRUE)
  upper1 <- quantile(ws1, probs = 0.95, na.rm = TRUE)
  tw1 <- pmax(pmin(ws1, upper1), lower1)
  
  lower2 <- quantile(ws2, probs = 0.05, na.rm = TRUE)
  upper2 <- quantile(ws2, probs = 0.95, na.rm = TRUE)
  tw2 <- pmax(pmin(ws2, upper2), lower2)
  
  lower3 <- quantile(ws3, probs = 0.05, na.rm = TRUE)
  upper3 <- quantile(ws3, probs = 0.95, na.rm = TRUE)
  tw3 <- pmax(pmin(ws3, upper3), lower3)
  
  pan_dat$cws1 <- pan_prod(ws1, pan_dat$ii)
  pan_dat$cws2 <- pan_prod(ws2, pan_dat$ii)
  pan_dat$tcw1 <- pan_prod(tw1, pan_dat$ii)
  pan_dat$tcw2 <- pan_prod(tw2, pan_dat$ii)
  pan_dat$cws3 <- pan_prod(ws3, pan_dat$ii)
  pan_dat$tcw3 <- pan_prod(tw3, pan_dat$ii)
  
  pan_dat_filtered <- pan_dat %>% filter(!is.na(lx))
  
  # Fit models
  naive_reg        <- lm(y ~ x, data = pan_dat)
  conf_reg         <- lm(y ~ x + z, data = pan_dat)
  ADL1             <- lm(y ~ x + lx + ly, data = pan_dat)
  ADL_contconf_reg <- lm(y ~ x + z + lx + ly, data = pan_dat)
  ADL_lagconf_reg  <- lm(y ~ x + z + lx + ly + lz, data = pan_dat)
  ADL2_reg         <- lm(y ~ x + lx + ly + l2y + z + lz, data = pan_dat)
  msm_cws1 <- geeglm(y ~ x + lx, data = pan_dat_filtered, weights = cws1,
                     id = ii, corstr = "independence")
  msm_cws2 <- geeglm(y ~ x + lx, data = pan_dat_filtered, weights = cws2, 
                     id = ii, corstr = "independence")
  msm_cws3 <- geeglm(y ~ x + lx + lcumx, data = pan_dat_filtered, 
                     weights = cws3, id = ii, corstr  = "independence")
  msm_tcw1 <- geeglm(y ~ x + lx, data = pan_dat_filtered, weights = tcw1, 
                     id = ii, corstr = "independence")
  msm_tcw2 <- geeglm(y ~ x + lx, data = pan_dat_filtered, weights = tcw2, 
                     id = ii, corstr = "independence")
  msm_tcw3 <- geeglm(y ~ x + lx + lcumx, data = pan_dat_filtered, 
                     weights = tcw3, id = ii, corstr  = "independence")
  
  
  # Collect results
  data.frame(
    bias_current = c(
      true_current - coef(naive_reg)["x"],
      true_current - coef(conf_reg)["x"],
      true_current - coef(ADL1)["x"],
      true_current - coef(ADL_contconf_reg)["x"],
      true_current - coef(ADL_lagconf_reg)["x"],
      true_current - coef(ADL2_reg)["x"],
      true_current - coef(msm_cws1)["x"],
      true_current - coef(msm_cws2)["x"],
      true_current - coef(msm_cws3)["x"],
      true_current - coef(msm_tcw1)["x"],
      true_current - coef(msm_tcw2)["x"],
      true_current - coef(msm_tcw3)["x"]
    ),
    bias_lagged = c(
      NA, 
      NA,
      true_lagged - adl_lagged(ADL1),
      true_lagged - adl_lagged(ADL_contconf_reg),
      true_lagged - adl_lagged(ADL_lagconf_reg),
      true_lagged - adl_lagged(ADL2_reg),
      true_lagged - coef(msm_cws1)["lx"],
      true_lagged - coef(msm_cws2)["lx"],
      true_lagged - coef(msm_cws3)["lx"],
      true_lagged - coef(msm_tcw1)["lx"],
      true_lagged - coef(msm_tcw2)["lx"],
      true_lagged - coef(msm_tcw3)["lx"]
    ),
    model = c("Regression Naive", "Regression Confounder", "ADL(1)",
              "ADL(1)+conf", "ADL(1)+lagconf", "ADL(2)", "MSM 1 Lag",
              "MSM 2 Lags", "MSM Cumulative", "MSM 1 Lag Truncated",
              "MSM 2 Lags Truncated", "MSM Cumulative Truncated"),
    true_current = true_current,  
    true_lagged  = true_lagged
  )
}


#----- Monte-Carlo Simulation
param_grid <- expand.grid(
  N          = c(100, 1500),
  gamma_name = c("gamma1", "gamma2"),
  eta_name   = c("eta0", "eta03")
)

run_param_combo <- function(N, gamma_name, eta_name, sim_n = n_sims) {
  
  gamma <- gamma_list[[gamma_name]]
  eta <<- eta_list[[eta_name]] 
  
  # Run sim_n replications
  results <- mclapply(1:sim_n, function(s) {
    tryCatch(
      run_simulation(N = N, T = 5, gamma = gamma, eta = eta),
      error   = function(e) NULL,
      warning = function(w) NULL
    )
  }, mc.cores = detectCores() - 1)
  
  # Combine and tag with parameters
  bind_rows(Filter(Negate(is.null), results), .id = "iteration") %>%
    mutate(
      N          = N,
      gamma_name = gamma_name,
      eta_name   = eta_name
    )
}

# Run across all parameter combinations
all_results <- pmap_dfr(
  list(
    N          = param_grid$N,
    gamma_name = param_grid$gamma_name,
    eta_name   = param_grid$eta_name     
  ),
  run_param_combo,
  sim_n = n_sims
)

# Summarise
summary_results <- all_results %>%
  group_by(model, N, gamma_name, eta_name) %>%
  summarise(
    true_current      = mean(true_current, na.rm= TRUE),
    true_lagged       = mean(true_lagged, na.rm = TRUE),
    mean_bias_current = mean(bias_current, na.rm = TRUE),
    mean_bias_lagged  = mean(bias_lagged,  na.rm = TRUE),
    rmse_current      = sqrt(mean(bias_current^2, na.rm = TRUE)),
    rmse_lagged       = sqrt(mean(bias_lagged^2,  na.rm = TRUE)),
    n_converged       = sum(!is.na(bias_current)),
    .groups = "drop"
  )


# Reshape to long format for easier plotting
model_order <- c(
  "Regression Naive", 
  "Regression Confounder", 
  "ADL(1)", 
  "ADL(1)+conf",
  "ADL(1)+lagconf", 
  "ADL(2)", 
  "MSM 1 Lag", 
  "MSM 2 Lags",
  "MSM Cumulative",
  "MSM 1 Lag Truncated", 
  "MSM 2 Lags Truncated",
  "MSM Cumulative Truncated"
)


summary_long_bias <- summary_results %>%
  select(model, N, gamma_name, eta_name,
         mean_bias_current, mean_bias_lagged,
         true_current, true_lagged) %>%
  group_by(gamma_name, eta_name) %>%
  mutate(
    true_current_label = mean(true_current, na.rm = TRUE),
    true_lagged_label  = mean(true_lagged,  na.rm = TRUE)
  ) %>%
  ungroup() %>%
  pivot_longer(
    cols      = c(mean_bias_current, mean_bias_lagged),
    names_to  = "effect",
    values_to = "bias"
  ) %>%
  mutate(
    true_value   = if_else(effect == "mean_bias_current", true_current, true_lagged),
    effect       = recode(effect,
                          "mean_bias_current" = "Current Treatment Effect",
                          "mean_bias_lagged"  = "Lagged Treatment Effect"),
    effect_label = paste0(effect, "\n(true = ", round(true_value, 2), ")"),
    N            = factor(N, levels = c(100, 1500)),
    model        = factor(model, levels = model_order),
    eta_name     = recode(eta_name,
                          "eta0"  = "No Direct Effect",
                          "eta03" = "Direct Effect")
  )

summary_long_rmse <- summary_results %>%
  select(model, N, gamma_name, eta_name,
         rmse_current, rmse_lagged,
         true_current, true_lagged) %>%
  group_by(gamma_name, eta_name) %>%
  mutate(
    true_current_label = mean(true_current, na.rm = TRUE),
    true_lagged_label  = mean(true_lagged,  na.rm = TRUE)
  ) %>%
  ungroup() %>%
  pivot_longer(
    cols      = c(rmse_current, rmse_lagged),
    names_to  = "effect",
    values_to = "rmse"
  ) %>%
  mutate(
    true_value   = if_else(effect == "rmse_current", true_current, true_lagged),
    effect       = recode(effect,
                          "rmse_current" = "Current Treatment Effect",
                          "rmse_lagged"  = "Lagged Treatment Effect"),
    effect_label = paste0(effect, "\n(true = ", round(true_value, 2), ")"),
    N            = factor(N, levels = c(100, 1500)),
    model        = factor(model, levels = model_order),
    eta_name     = recode(eta_name,
                          "eta0"  = "No Direct Effect",
                          "eta03" = "Direct Effect")
  )


plot_bias <- function(gamma, eta, title) {
  summary_long_bias %>%
    filter(gamma_name == gamma, eta_name == eta, !is.na(bias)) %>%
    mutate(N = droplevels(N)) %>%
    ggplot(aes(x = model, y = bias, color = N, group = N)) +
    geom_point(size = 3) +
    geom_line() +
    geom_hline(yintercept = 0, linetype = "dashed", color = "grey30") +
    facet_wrap(~ effect_label, scales = "free_y") +
    coord_flip() +
    scale_color_brewer(palette = "Set1") +
    labs(title = title, x = NULL, y = "Mean Bias", color = "N") +
    theme_bw() +
    theme(
      legend.position  = "bottom",
      strip.background = element_rect(fill = "grey90"),
      strip.text       = element_text(face = "bold")
    )
}

plot_rmse <- function(gamma, eta, title) {
  summary_long_rmse %>%
    filter(gamma_name == gamma, eta_name == eta, !is.na(rmse)) %>%
    mutate(N = droplevels(N)) %>%
    ggplot(aes(x = model, y = rmse, color = N, group = N)) +
    geom_point(size = 3) +
    geom_line() +
    facet_wrap(~ effect_label, scales = "free_y") +
    coord_flip() +
    expand_limits(y = 0) +
    scale_color_brewer(palette = "Set1") +
    labs(title = title, x = NULL, y = "RMSE", color = "N") +
    theme_bw() +
    theme(
      legend.position  = "bottom",
      strip.background = element_rect(fill = "grey90"),
      strip.text       = element_text(face = "bold")
    )
}

# Bias plots
p1_bias <- plot_bias("gamma1", "No Direct Effect",
                     "No Treatment-Induced Confounding, No Direct Effect")
p2_bias <- plot_bias("gamma2", "No Direct Effect",
                     "Treatment-Induced Confounding, No Direct Effect")
p3_bias <- plot_bias("gamma1", "Direct Effect",
                     "No Treatment-Induced Confounding, Direct Effect")
p4_bias <- plot_bias("gamma2", "Direct Effect",
                     "Treatment-Induced Confounding, Direct Effect")

plots_bias <- list(
  p1 = p1_bias,
  p2 = p2_bias,
  p3 = p3_bias,
  p4 = p4_bias
)
saveRDS(plots_bias, file = "MSM/results/plots_bias.rds")

# RMSE plots
p1_rmse <- plot_rmse("gamma1", "No Direct Effect",
                     "No Treatment-Induced Confounding, No Direct Effect")
p2_rmse <- plot_rmse("gamma2", "No Direct Effect",
                     "Treatment-Induced Confounding, No Direct Effect")
p3_rmse <- plot_rmse("gamma1", "Direct Effect",
                     "No Treatment-Induced Confounding, Direct Effect")
p4_rmse <- plot_rmse("gamma2", "Direct Effect",
                     "Treatment-Induced Confounding, Direct Effect")

plots_rmse <- list(
  p1 = p1_rmse,
  p2 = p2_rmse,
  p3 = p3_rmse,
  p4 = p4_rmse
)
saveRDS(plots_rmse, file = "MSM/results/plots_rmse.rds")

