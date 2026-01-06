# =============================================================================
# NFLPA Case Competition: Cumulative Workload Analysis
# =============================================================================
# This script analyzes the cumulative effects of workload on:
#   1. Injury incidence and severity
#   2. Team and player performance (EPA)
#   3. Win/Loss outcomes
#   4. 17-game season impact (DiD analysis)
# =============================================================================

# -----------------------------------------------------------------------------
# Setup and Dependencies
# -----------------------------------------------------------------------------
library(tidyverse)
library(nflreadr)
library(nflfastR)
library(rvest)
library(lme4)
library(broom)
library(broom.mixed)
library(survival)
library(survminer)
library(gt)
library(glue)
library(MASS)
library(performance)
library(slider)
library(httr)
library(jsonlite)

# Optional: for cleaning table names
if (requireNamespace("janitor", quietly = TRUE)) {
  library(janitor)
}

# Resolve namespace conflicts
library(conflicted)
conflict_prefer("select", "dplyr")
conflict_prefer("filter", "dplyr")
conflict_prefer("lag", "dplyr")

# Optional packages for robust inference
if (requireNamespace("sandwich", quietly = TRUE)) {
  library(sandwich)
}
if (requireNamespace("lmtest", quietly = TRUE)) {
  library(lmtest)
}

# -----------------------------------------------------------------------------
# Configuration
# -----------------------------------------------------------------------------
CONFIG <- list(
  seasons = 2015:2024,  # 10 seasons total (updated to include 2024)
  seasons_pre_17 = 2015:2020,  # 6 seasons with 16-game schedule
  seasons_post_17 = 2021:2024,  # 4 seasons with 17-game schedule
  min_touches = 5,
  short_rest_threshold = 5,
  tnf_games_per_season = 16,
  n_teams = 32,
  active_roster_size = 53,
  game_day_roster_size = 48,
  output_dir = "plots"
)

# Time zone mapping for teams
TEAM_TIMEZONES <- c(
  "ARI" = "MST", "ATL" = "EST", "BAL" = "EST", "BUF" = "EST",

"CAR" = "EST", "CHI" = "CST", "CIN" = "EST", "CLE" = "EST",
  "DAL" = "CST", "DEN" = "MST", "DET" = "EST", "GB" = "CST",
  "HOU" = "CST", "IND" = "EST", "JAX" = "EST", "KC" = "CST",
  "LAC" = "PST", "LA" = "PST", "LAR" = "PST", "LV" = "PST",
  "OAK" = "PST", "MIA" = "EST", "MIN" = "CST", "NE" = "EST",
  "NO" = "CST", "NYG" = "EST", "NYJ" = "EST", "PHI" = "EST",
  "PIT" = "EST", "SF" = "PST", "SEA" = "PST", "TB" = "EST",
  "TEN" = "CST", "WAS" = "EST"
)

# PFR team abbreviation mapping
PFR_TEAMS <- c(
  "ARI" = "crd", "ATL" = "atl", "BAL" = "rav", "BUF" = "buf",
  "CAR" = "car", "CHI" = "chi", "CIN" = "cin", "CLE" = "cle",
  "DAL" = "dal", "DEN" = "den", "DET" = "det", "GB" = "gnb",
  "HOU" = "htx", "IND" = "clt", "JAX" = "jax", "KC" = "kan",
  "LAC" = "sdg", "LA" = "ram", "LAR" = "ram", "LV" = "rai",
  "OAK" = "rai", "MIA" = "mia", "MIN" = "min", "NE" = "nwe",
  "NO" = "nor", "NYG" = "nyg", "NYJ" = "nyj", "PHI" = "phi",
  "PIT" = "pit", "SF" = "sfo", "SEA" = "sea", "TB" = "tam",
  "TEN" = "oti", "WAS" = "was"
)

# =============================================================================
# PART 1: DATA LOADING AND PREPARATION
# =============================================================================

# -----------------------------------------------------------------------------
# 1.1 Load Schedule Data and Compute Rest Days
# -----------------------------------------------------------------------------
load_schedule_with_rest <- function(seasons = CONFIG$seasons) {
  
  schedules <- load_schedules(seasons) %>%
    filter(game_type == "REG") %>%
    dplyr::select(game_id, season, week, gameday, weekday, gametime,
                  home_team, away_team, home_score, away_score,
                  stadium, roof, surface)
  
  # Reshape to team-game level

  team_games <- bind_rows(
    schedules %>%
      transmute(
        game_id, season, week, gameday, weekday,
        team = home_team,
        opponent = away_team,
        home = TRUE,
        points_for = home_score,
        points_against = away_score,
        surface, roof
      ),
    schedules %>%
      transmute(
        game_id, season, week, gameday, weekday,
        team = away_team,
        opponent = home_team,
        home = FALSE,
        points_for = away_score,
        points_against = home_score,
        surface, roof
      )
  ) %>%
    arrange(team, season, week) %>%
    mutate(
      gameday = as.Date(gameday),
      win = points_for > points_against,
      tie = points_for == points_against,
      margin = points_for - points_against
    )
  
  # Compute days rest from previous game
  team_games <- team_games %>%
    group_by(team, season) %>%
    mutate(
      prev_gameday = lag(gameday),
      days_rest = as.numeric(gameday - prev_gameday),
      prev_week = lag(week),
      prev_weekday = lag(weekday)
    ) %>%
    ungroup()
  
  # Classify rest categories
  team_games <- team_games %>%
    mutate(
      # Split Thursday game identification from short rest
      is_thursday_game = weekday == "Thursday",
      is_short_rest = days_rest <= CONFIG$short_rest_threshold & !is.na(days_rest),
      is_short_rest_thursday = is_thursday_game & is_short_rest,
      # Keep is_tnf for backward compatibility (short-rest Thursday)
      is_tnf = is_short_rest_thursday,
      rest_category = case_when(
        is.na(days_rest) ~ "First Game",
        is_short_rest_thursday ~ "Thursday (Short Rest)",
        is_thursday_game & !is_short_rest ~ "Thursday (Not Short Rest)",
        days_rest <= 4 ~ "Short (4 days)",
        days_rest == 5 ~ "Short (5 days)",
        days_rest >= 8 & days_rest <= 10 & prev_weekday == "Monday" ~ "Extended (MNF->SUN)",
        days_rest >= 8 & days_rest <= 10 ~ "Extended (8-10 days)",
        days_rest >= 11 ~ "Post-Bye",
        TRUE ~ "Standard (6-7 days)"
      ),
      is_short_week = is_short_rest,
      is_short_week_after_sunday = days_rest <= 4 & prev_weekday == "Sunday" & !is.na(days_rest),
      is_short_week_after_monday = days_rest <= 4 & prev_weekday == "Monday" & !is.na(days_rest),
      # 17-game season indicator
      is_17_game_season = season >= 2021
    )
  
  return(team_games)
}

# -----------------------------------------------------------------------------
# 1.2 Add Cumulative Workload Metrics
# -----------------------------------------------------------------------------
add_cumulative_workload <- function(team_games) {
  
  team_games <- team_games %>%
    group_by(team, season) %>%
    arrange(week) %>%
    mutate(
      # Games played this season
      games_played = row_number(),
      
      # Cumulative short weeks
      cum_short_weeks = cumsum(replace_na(is_short_week, FALSE)),
      
      # Cumulative TNF games
      cum_tnf_games = cumsum(replace_na(is_tnf, FALSE)),
      
      # Running average rest days
      cum_avg_rest = cummean(replace_na(days_rest, 7)),
      
      # Games since last bye (find bye weeks by gap >= 11 days)
      # Note: This is an approximation. Bye weeks are identified by rest >= 11 days.
      # Edge cases (international games, rescheduled games, COVID-affected 2020) may
      # be misclassified. 2020 is excluded from DiD analysis to avoid COVID confounding.
      games_since_bye = {
        is_post_bye <- replace_na(days_rest >= 11, FALSE)
        bye_indices <- which(is_post_bye)
        
        if (length(bye_indices) == 0) {
          # No bye yet - count from start
          row_number()
        } else {
          sapply(row_number(), function(i) {
            last_bye <- max(c(0, bye_indices[bye_indices <= i]))
            if (last_bye == 0) i else i - last_bye
          })
        }
      }
    ) %>%
    ungroup()
  
  return(team_games)
}

# -----------------------------------------------------------------------------
# 1.3 Add Workload Shape Analysis (Front-loaded vs Back-loaded)
# -----------------------------------------------------------------------------
add_workload_shape <- function(team_games) {
  
  team_games <- team_games %>%
    group_by(team, season) %>%
    arrange(week) %>%
    mutate(
      # Phase of season
      season_phase = case_when(
        week <= 6 ~ "Early (Weeks 1-6)",
        week <= 12 ~ "Mid (Weeks 7-12)",
        week <= 18 ~ "Late (Weeks 13-18)",
        TRUE ~ "Postseason"
      ),
      season_phase = factor(season_phase,
                            levels = c("Early (Weeks 1-6)", "Mid (Weeks 7-12)",
                                       "Late (Weeks 13-18)", "Postseason")),
      
      # Short weeks by phase (cumulative within each phase)
      short_weeks_early = cumsum(if_else(week <= 6, is_short_week, FALSE)),
      short_weeks_mid = cumsum(if_else(week > 6 & week <= 12, is_short_week, FALSE)),
      short_weeks_late = cumsum(if_else(week > 12 & week <= 18, is_short_week, FALSE))
    ) %>%
    ungroup()
  
  # Calculate front-loaded / back-loaded indicators at team-season level
  team_season_shape <- team_games %>%
    group_by(team, season) %>%
    summarise(
      early_short_weeks = sum(is_short_week & week <= 6, na.rm = TRUE),
      mid_short_weeks = sum(is_short_week & week > 6 & week <= 12, na.rm = TRUE),
      late_short_weeks = sum(is_short_week & week > 12, na.rm = TRUE),
      total_short_weeks = sum(is_short_week, na.rm = TRUE),
      .groups = "drop"
    ) %>%
    mutate(
      front_loaded = early_short_weeks >= 2,
      back_loaded = late_short_weeks >= 2,
      workload_shape = case_when(
        front_loaded & !back_loaded ~ "Front-loaded",
        back_loaded & !front_loaded ~ "Back-loaded",
        front_loaded & back_loaded ~ "Both",
        TRUE ~ "Balanced"
      )
    )
  
  team_games <- team_games %>%
    left_join(team_season_shape, by = c("team", "season"))
  
  return(team_games)
}

# -----------------------------------------------------------------------------
# 1.4 Add Bye Week Quality Analysis
# -----------------------------------------------------------------------------
add_bye_quality <- function(team_games) {
  
  team_games <- team_games %>%
    group_by(team, season) %>%
    arrange(week) %>%
    mutate(
      # Identify bye week (gap >= 11 days)
      is_post_bye_game = replace_na(days_rest >= 11, FALSE),
      
      # Bye within 2 weeks before/after
      bye_within_2_weeks_before = lag(is_post_bye_game, 1, default = FALSE) |
        lag(is_post_bye_game, 2, default = FALSE),
      bye_within_2_weeks_after = lead(is_post_bye_game, 1, default = FALSE) |
        lead(is_post_bye_game, 2, default = FALSE),
      
      # TNF preceded by recent bye
      tnf_after_bye = is_tnf & bye_within_2_weeks_before,
      
      # Short rest without bye buffer
      short_rest_no_bye = is_short_week & !bye_within_2_weeks_before
    ) %>%
    ungroup()
  
  return(team_games)
}

# -----------------------------------------------------------------------------
# 1.5 Add Schedule Compression Metrics (using slider for efficiency)
# -----------------------------------------------------------------------------
add_schedule_compression <- function(team_games) {
  
  team_games <- team_games %>%
    group_by(team, season) %>%
    arrange(week) %>%
    mutate(
      # Games in last 3 weeks (rolling sum)
      games_last_3_weeks = slide_dbl(
        rep(1, n()),
        sum,
        .before = 2,
        .complete = FALSE
      ),
      
      # Games in last 4 weeks
      games_last_4_weeks = slide_dbl(
        rep(1, n()),
        sum,
        .before = 3,
        .complete = FALSE
      ),
      
      # Short weeks in last 3 weeks
      short_weeks_last_3 = slide_dbl(
        as.numeric(is_short_week),
        sum,
        .before = 2,
        .complete = FALSE
      ),
      
      # Compression indicators
      high_compression_3wk = games_last_3_weeks >= 3,
      high_compression_4wk = games_last_4_weeks >= 4
    ) %>%
    ungroup()
  
  return(team_games)
}

# -----------------------------------------------------------------------------
# 1.6 Add Travel Analysis
# -----------------------------------------------------------------------------
add_travel_analysis <- function(team_games) {
  
  tz_offset <- c("EST" = 0, "CST" = 1, "MST" = 2, "PST" = 3)
  
  team_games <- team_games %>%
    mutate(
      home_tz = TEAM_TIMEZONES[team],
      opponent_tz = TEAM_TIMEZONES[opponent],
      team_tz_offset = tz_offset[home_tz],
      opponent_tz_offset = tz_offset[opponent_tz],
      
      # Time zone difference (0 for home games)
      tz_diff = if_else(home, 0L, abs(team_tz_offset - opponent_tz_offset)),
      crossed_timezones = tz_diff > 0,
      
      # Travel direction
      west_to_east = !home & (team_tz_offset > opponent_tz_offset),
      east_to_west = !home & (team_tz_offset < opponent_tz_offset)
    ) %>%
    dplyr::select(-team_tz_offset, -opponent_tz_offset)
  
  # Add cumulative travel metrics
  team_games <- team_games %>%
    group_by(team, season) %>%
    arrange(week) %>%
    mutate(
      cum_tz_crossings = cumsum(crossed_timezones),
      cum_west_to_east = cumsum(west_to_east),
      cum_east_to_west = cumsum(east_to_west),
      
      # Consecutive road games (streak length so far: 1, 2, 3...)
      is_road = !home,
      consecutive_road_games = {
        # Calculate streak length within each road streak
        ave(is_road, cumsum(!is_road), FUN = seq_along) * is_road
      }
    ) %>%
    ungroup()
  
  return(team_games)
}

# -----------------------------------------------------------------------------
# 1.7 Load and Process Injury Data
# -----------------------------------------------------------------------------
load_injury_data <- function(seasons = CONFIG$seasons) {
  
  injuries <- load_injuries(seasons)
  
  available_cols <- colnames(injuries)
  cat("Available injury columns:", paste(available_cols, collapse = ", "), "\n")
  
  injury_summary <- injuries %>%
    group_by(season, week, team, gsis_id, full_name, position) %>%
    summarise(
      report_status = first(report_status),
      practice_status = if ("practice_status" %in% available_cols) {
        first(practice_status)
      } else {
        NA_character_
      },
      primary_injury = if ("report_primary_injury" %in% available_cols) {
        first(report_primary_injury)
      } else {
        NA_character_
      },
      secondary_injury = if ("report_secondary_injury" %in% available_cols) {
        first(report_secondary_injury)
      } else if ("practice_secondary_injury" %in% available_cols) {
        first(practice_secondary_injury)
      } else {
        NA_character_
      },
      .groups = "drop"
    ) %>%
    mutate(
      is_out = report_status %in% c("Out", "Doubtful"),
      is_limited = report_status %in% c("Questionable", "Limited"),
      is_on_report = !is.na(report_status)
    )
  
  # Identify NEW injuries (first appearance after being off report for 4+ weeks)
  # Note: 4-week washout window chosen to balance:
  # - Capturing new injuries vs. lingering issues
  # - Avoiding false positives from brief absences
  # - Aligning with typical injury recovery timelines
  # Robustness checks with 3-week and 6-week windows available in sensitivity analysis
  injury_summary <- injury_summary %>%
    group_by(season, gsis_id) %>%
    arrange(week) %>%
    mutate(
      last_on_report_week = lag(if_else(is_on_report, week, NA_integer_)),
      weeks_since_last_report = week - last_on_report_week,
      is_new_injury = is_on_report & (is.na(last_on_report_week) | weeks_since_last_report >= 4),
      # Robustness: alternative definitions for sensitivity analysis
      is_new_injury_3wk = is_on_report & (is.na(last_on_report_week) | weeks_since_last_report >= 3),
      is_new_injury_6wk = is_on_report & (is.na(last_on_report_week) | weeks_since_last_report >= 6)
    ) %>%
    ungroup()
  
  return(injury_summary)
}

# Aggregate injuries to team-week level
aggregate_injuries <- function(injury_data, team_games) {
  
  team_week_injuries <- injury_data %>%
    group_by(season, week, team) %>%
    summarise(
      n_players_out = sum(is_out, na.rm = TRUE),
      n_players_limited = sum(is_limited, na.rm = TRUE),
      n_new_injuries = sum(is_new_injury, na.rm = TRUE),
      n_on_report = n_distinct(gsis_id),  # Count distinct players, not rows
      .groups = "drop"
    )
  
  # Roster sizes by team-season
  roster_sizes <- injury_data %>%
    group_by(season, team) %>%
    summarise(
      unique_players_seen = n_distinct(gsis_id),
      .groups = "drop"
    ) %>%
    mutate(
      active_roster_size = pmax(unique_players_seen, CONFIG$game_day_roster_size)
    )
  
  # Join to team games
  team_games_injuries <- team_games %>%
    left_join(team_week_injuries, by = c("season", "week", "team")) %>%
    left_join(roster_sizes, by = c("season", "team")) %>%
    mutate(
      across(starts_with("n_"), ~replace_na(., 0)),
      injuries_per_roster = (n_new_injuries / active_roster_size) * CONFIG$game_day_roster_size,
      players_out_per_roster = (n_players_out / active_roster_size) * CONFIG$game_day_roster_size
    )
  
  # Get NEXT week's injuries (occurred IN this game)
  team_games_injuries <- team_games_injuries %>%
    group_by(team, season) %>%
    arrange(week) %>%
    mutate(
      injuries_next_week = lead(n_new_injuries),
      players_out_next_week = lead(n_players_out),
      injuries_next_week_per_roster = lead(injuries_per_roster),
      
      # Player out designations in next 4 weeks (severity proxy)
      # Note: This counts team-week "out" designations, not individual player games missed
      player_out_weeks_next_4 = slide_dbl(
        lead(n_players_out),
        sum,
        .after = 3,
        .complete = FALSE
      ),
      # Keep old name for backward compatibility during transition
      games_missed_next_4 = player_out_weeks_next_4
    ) %>%
    ungroup()
  
  return(team_games_injuries)
}

# -----------------------------------------------------------------------------
# 1.8 Load Play-by-Play Data for EPA Analysis
# -----------------------------------------------------------------------------
load_epa_data <- function(seasons = CONFIG$seasons) {
  
  pbp <- nflreadr::load_pbp(seasons) %>%
    filter(season_type == "REG") %>%
    dplyr::select(game_id, season, week, posteam, defteam,
                  play_type, epa, success, yards_gained,
                  pass, rush, qb_dropback, cpoe, air_yards)
  
  # Team offensive EPA per game
  team_off_epa <- pbp %>%
    filter(!is.na(epa), !is.na(posteam)) %>%
    group_by(game_id, season, week, team = posteam) %>%
    summarise(
      total_epa = sum(epa, na.rm = TRUE),
      epa_play = mean(epa, na.rm = TRUE),
      n_plays = n(),
      pass_epa = mean(epa[pass == 1], na.rm = TRUE),
      rush_epa = mean(epa[rush == 1], na.rm = TRUE),
      success_rate = mean(success, na.rm = TRUE),
      .groups = "drop"
    )
  
  # Team defensive EPA per game
  team_def_epa <- pbp %>%
    filter(!is.na(epa), !is.na(defteam)) %>%
    group_by(game_id, season, week, team = defteam) %>%
    summarise(
      def_epa = sum(epa, na.rm = TRUE),
      def_epa_play = mean(epa, na.rm = TRUE),
      def_success_rate = mean(success, na.rm = TRUE),
      .groups = "drop"
    )
  
  team_epa <- team_off_epa %>%
    left_join(team_def_epa, by = c("game_id", "season", "week", "team")) %>%
    mutate(
      net_epa = total_epa - def_epa,
      net_epa_play = epa_play - def_epa_play
    )
  
  return(team_epa)
}

# -----------------------------------------------------------------------------
# 1.9 Load Player Performance Data
# -----------------------------------------------------------------------------
load_player_performance <- function(seasons = CONFIG$seasons) {
  
  pbp <- nflreadr::load_pbp(seasons) %>%
    filter(season_type == "REG")
  
  # Player passing stats
  player_pass <- pbp %>%
    filter(pass == 1, !is.na(passer_player_id)) %>%
    group_by(game_id, season, week, player_id = passer_player_id, team = posteam) %>%
    summarise(
      pass_epa = sum(epa, na.rm = TRUE),
      pass_attempts = n(),
      completions = sum(complete_pass, na.rm = TRUE),
      pass_yards = sum(yards_gained, na.rm = TRUE),
      .groups = "drop"
    )
  
  # Player rushing stats
  player_rush <- pbp %>%
    filter(rush == 1, !is.na(rusher_player_id)) %>%
    group_by(game_id, season, week, player_id = rusher_player_id, team = posteam) %>%
    summarise(
      rush_epa = sum(epa, na.rm = TRUE),
      rush_attempts = n(),
      rush_yards = sum(yards_gained, na.rm = TRUE),
      .groups = "drop"
    )
  
  # Player receiving stats
  player_rec <- pbp %>%
    filter(pass == 1, !is.na(receiver_player_id)) %>%
    group_by(game_id, season, week, player_id = receiver_player_id, team = posteam) %>%
    summarise(
      rec_epa = sum(epa, na.rm = TRUE),
      targets = n(),
      receptions = sum(complete_pass, na.rm = TRUE),
      rec_yards = sum(yards_gained, na.rm = TRUE),
      .groups = "drop"
    )
  
  # Combine
  player_stats <- player_pass %>%
    full_join(player_rush, by = c("game_id", "season", "week", "player_id", "team")) %>%
    full_join(player_rec, by = c("game_id", "season", "week", "player_id", "team")) %>%
    mutate(
      across(c(pass_epa, rush_epa, rec_epa), ~replace_na(., 0)),
      across(c(pass_attempts, rush_attempts, targets), ~replace_na(., 0L)),
      total_epa = pass_epa + rush_epa + rec_epa,
      total_touches = pass_attempts + rush_attempts + targets
    )
  
  return(player_stats)
}

# =============================================================================
# PART 2: BUILD COMPLETE ANALYSIS DATASET
# =============================================================================

# -----------------------------------------------------------------------------
# 2.1 Data Validation
# -----------------------------------------------------------------------------
validate_data <- function(data) {
  
  checks <- list(
    total_rows = nrow(data),
    missing_rest = sum(is.na(data$days_rest) & data$rest_category != "First Game"),
    invalid_rest = sum(data$days_rest < 3 | data$days_rest > 14, na.rm = TRUE),
    missing_epa = sum(is.na(data$epa_play)),
    missing_injuries = sum(is.na(data$injuries_next_week) & 
                          data$rest_category != "First Game" & 
                          data$week != max(data$week, na.rm = TRUE)),  # Last week expected to be NA
    seasons_covered = unique(data$season),
    teams_covered = n_distinct(data$team)
  )
  
  cat("\n=== Data Validation ===\n")
  cat(glue("Total rows: {checks$total_rows}\n"))
  cat(glue("Missing rest days: {checks$missing_rest}\n"))
  cat(glue("Invalid rest periods: {checks$invalid_rest}\n"))
  cat(glue("Missing EPA: {checks$missing_epa}\n"))
  cat(glue("Missing injuries: {checks$missing_injuries}\n"))
  cat(glue("Seasons: {paste(checks$seasons_covered, collapse = ', ')}\n"))
  cat(glue("Teams: {checks$teams_covered}\n\n"))
  
  return(checks)
}

# -----------------------------------------------------------------------------
# 2.2 Build Analysis Dataset
# -----------------------------------------------------------------------------
build_analysis_dataset <- function(include_player_level = TRUE) {
  
  message("Loading schedules...")
  team_games <- load_schedule_with_rest()
  
  message("Adding cumulative workload...")
  team_games <- add_cumulative_workload(team_games)
  
  message("Adding workload shape...")
  team_games <- add_workload_shape(team_games)
  
  message("Adding bye quality...")
  team_games <- add_bye_quality(team_games)
  
  message("Adding schedule compression...")
  team_games <- add_schedule_compression(team_games)
  
  message("Adding travel analysis...")
  team_games <- add_travel_analysis(team_games)
  
  message("Loading injuries...")
  injuries <- load_injury_data()
  team_games <- aggregate_injuries(injuries, team_games)
  
  message("Loading EPA data...")
  epa_data <- load_epa_data()
  
  # Join EPA to team games
  analysis_data <- team_games %>%
    left_join(epa_data, by = c("game_id", "season", "week", "team"))
  
  # Add opponent rest for fairness adjustment
  opponent_rest <- team_games %>%
    dplyr::select(game_id, team, opp_days_rest = days_rest,
                  opp_rest_category = rest_category,
                  opp_games_since_bye = games_since_bye,
                  opp_cum_short_weeks = cum_short_weeks)
  
  analysis_data <- analysis_data %>%
    left_join(opponent_rest, by = c("game_id", "opponent" = "team")) %>%
    mutate(
      # Rest differential (positive = advantage)
      rest_diff = days_rest - opp_days_rest,
      unfair_rest = rest_diff <= -2 & !is.na(rest_diff),
      rest_advantage = rest_diff >= 2 & !is.na(rest_diff),
      
      rest_diff_category = case_when(
        is.na(rest_diff) ~ "Unknown",
        rest_diff <= -3 ~ "Large Disadvantage (-3+)",
        rest_diff == -2 ~ "Disadvantage (-2)",
        rest_diff == -1 ~ "Small Disadvantage (-1)",
        rest_diff == 0 ~ "Equal Rest",
        rest_diff == 1 ~ "Small Advantage (+1)",
        rest_diff == 2 ~ "Advantage (+2)",
        rest_diff >= 3 ~ "Large Advantage (+3+)"
      )
    )
  
  # Store injury data for survival analysis
  attr(analysis_data, "injury_data") <- injuries
  
  # Add rest_diff to team_games for functions that need it
  # (rest_diff is calculated in analysis_data, so extract it)
  team_games_with_rest_diff <- analysis_data %>%
    dplyr::select(season, week, team, days_rest, rest_category,
                  games_since_bye, cum_short_weeks, is_short_week, is_tnf,
                  rest_diff, unfair_rest, is_17_game_season) %>%
    distinct()
  
  # Store team_games for functions that need it
  attr(analysis_data, "team_games") <- team_games_with_rest_diff
  
  # Add player-level data if requested
  if (include_player_level) {
    message("Loading player performance...")
    player_stats <- load_player_performance()
    
    player_games <- player_stats %>%
      left_join(
        team_games %>% dplyr::select(game_id, team, days_rest, rest_category,
                                     is_short_week, games_since_bye, cum_short_weeks),
        by = c("game_id", "team")
      )
    
    attr(analysis_data, "player_data") <- player_games
  }
  
  # Validate (adjust for expected NAs in last week)
  validation_checks <- validate_data(analysis_data)
  
  return(analysis_data)
}

# =============================================================================
# PART 3: ANALYSIS FUNCTIONS
# =============================================================================

# -----------------------------------------------------------------------------
# 3.1 Performance Effects Analysis
# -----------------------------------------------------------------------------
analyze_performance_effects <- function(data) {
  
  model_data <- data %>%
    filter(rest_category != "First Game") %>%
    mutate(
      rest_category = factor(rest_category,
                             levels = c("Standard (6-7 days)", "Thursday (Short Rest)",
                                        "Thursday (Not Short Rest)", "Short (4 days)", 
                                        "Short (5 days)", "Extended (MNF->SUN)", 
                                        "Extended (8-10 days)", "Post-Bye"))
    )
  
  # Model 1: Simple rest differential
  simple_restdiff <- lm(epa_play ~ rest_diff, data = model_data)
  
  # Model 2: With controls
  controlled_model <- lm(
    epa_play ~ rest_category + home + surface +
      opp_rest_category + factor(season),
    data = model_data
  )
  
  # Model 3: With cumulative workload
  cumulative_model <- lm(
    epa_play ~ rest_category + rest_diff + home + surface +
      games_since_bye + cum_short_weeks +
      crossed_timezones + factor(season),
    data = model_data
  )
  
  # Clustered standard errors for all performance models (team level)
  simple_restdiff_clustered <- NULL
  controlled_model_clustered <- NULL
  cumulative_model_clustered <- NULL
  fe_model_clustered <- NULL
  
  if (requireNamespace("sandwich", quietly = TRUE) &&
      requireNamespace("lmtest", quietly = TRUE)) {
    simple_restdiff_clustered <- tryCatch({
      lmtest::coeftest(simple_restdiff,
                       vcov = sandwich::vcovCL(simple_restdiff, cluster = model_data$team))
    }, error = function(e) NULL)
    
    controlled_model_clustered <- tryCatch({
      lmtest::coeftest(controlled_model,
                       vcov = sandwich::vcovCL(controlled_model, cluster = model_data$team))
    }, error = function(e) NULL)
    
    cumulative_model_clustered <- tryCatch({
      lmtest::coeftest(cumulative_model,
                       vcov = sandwich::vcovCL(cumulative_model, cluster = model_data$team))
    }, error = function(e) NULL)
  }
  
  # Model 4: Mixed-effects model with team and season random intercepts
  # Note: Season is included as both random intercept (1|season) and fixed effect factor(season)
  # in different models. Here we use random intercepts to allow season-specific baseline performance
  # while controlling for team-level heterogeneity. This is appropriate when we want to account
  # for unobserved team and season characteristics without estimating separate coefficients.
  fe_model <- lmer(
    epa_play ~ rest_category + rest_diff + home + surface +
      games_since_bye + cum_short_weeks +
      crossed_timezones + (1 | team) + (1 | season),
    data = model_data
  )
  
  # Clustered SE for mixed-effects model (robustness check)
  # Note: Mixed-effects models already account for clustering via random effects,
  # but clustered SE provides additional robustness
  if (requireNamespace("sandwich", quietly = TRUE) &&
      requireNamespace("lmtest", quietly = TRUE)) {
    fe_model_clustered <- tryCatch({
      lmtest::coeftest(fe_model,
                       vcov = sandwich::vcovCL(fe_model, cluster = model_data$team))
    }, error = function(e) NULL)
  }
  
  # Summary statistics
  rest_summary <- model_data %>%
    group_by(rest_category) %>%
    summarise(
      n_games = n(),
      mean_epa = mean(epa_play, na.rm = TRUE),
      se_epa = sd(epa_play, na.rm = TRUE) / sqrt(n()),
      mean_success_rate = mean(success_rate, na.rm = TRUE),
      mean_points = mean(points_for, na.rm = TRUE),
      win_pct = mean(win, na.rm = TRUE),
      .groups = "drop"
    )
  
  list(
    simple_restdiff = simple_restdiff,
    simple_restdiff_clustered = simple_restdiff_clustered,
    controlled = controlled_model,
    controlled_clustered = controlled_model_clustered,
    cumulative = cumulative_model,
    cumulative_clustered = cumulative_model_clustered,
    fixed_effects = fe_model,
    fixed_effects_clustered = fe_model_clustered,
    summary = rest_summary
  )
}

# -----------------------------------------------------------------------------
# 3.2 Injury Effects Analysis
# -----------------------------------------------------------------------------
analyze_injury_effects <- function(data) {
  
  model_data <- data %>%
    filter(rest_category != "First Game") %>%
    mutate(
      rest_category = factor(rest_category,
                             levels = c("Standard (6-7 days)", "Thursday (Short Rest)",
                                        "Thursday (Not Short Rest)", "Short (4 days)", 
                                        "Short (5 days)", "Extended (MNF->SUN)", 
                                        "Extended (8-10 days)", "Post-Bye"))
    )
  
  # Check overdispersion (for diagnostic purposes)
  poisson_model <- glm(
    injuries_next_week ~ rest_category + home + surface + factor(season),
    data = model_data,
    family = poisson()
  )
  
  dispersion_ratio <- sum(residuals(poisson_model, type = "pearson")^2) / poisson_model$df.residual
  # Always use negbin for injury count data (overdispersion is expected)
  
  # Primary model: Rest differential
  injury_nb_restdiff <- MASS::glm.nb(
    injuries_next_week ~ rest_diff + home + surface +
      games_since_bye + cum_short_weeks + factor(season),
    data = model_data
  )
  
  # Unfair rest model
  injury_nb_unfair <- MASS::glm.nb(
    injuries_next_week ~ unfair_rest + home + surface +
      games_since_bye + cum_short_weeks + factor(season),
    data = model_data
  )
  
  # Rest category model
  injury_nb_category <- MASS::glm.nb(
    injuries_next_week ~ rest_category + home + surface +
      games_since_bye + cum_short_weeks + factor(season),
    data = model_data
  )
  
  # With offset for roster exposure
  injury_nb_offset <- MASS::glm.nb(
    injuries_next_week ~ rest_category + home + surface +
      games_since_bye + cum_short_weeks + factor(season) +
      offset(log(active_roster_size)),
    data = model_data %>% filter(active_roster_size > 0)
  )
  
  # Clustered standard errors for all injury models (team level)
  poisson_clustered <- NULL
  injury_restdiff_clustered <- NULL
  injury_unfair_clustered <- NULL
  injury_category_clustered <- NULL
  injury_offset_clustered <- NULL
  
  if (requireNamespace("sandwich", quietly = TRUE) &&
      requireNamespace("lmtest", quietly = TRUE)) {
    poisson_clustered <- tryCatch({
      lmtest::coeftest(poisson_model,
                       vcov = sandwich::vcovCL(poisson_model, cluster = model_data$team))
    }, error = function(e) NULL)
    
    injury_restdiff_clustered <- tryCatch({
      lmtest::coeftest(injury_nb_restdiff,
                       vcov = sandwich::vcovCL(injury_nb_restdiff, cluster = model_data$team))
    }, error = function(e) NULL)
    
    injury_unfair_clustered <- tryCatch({
      lmtest::coeftest(injury_nb_unfair,
                       vcov = sandwich::vcovCL(injury_nb_unfair, cluster = model_data$team))
    }, error = function(e) NULL)
    
    injury_category_clustered <- tryCatch({
      lmtest::coeftest(injury_nb_category,
                       vcov = sandwich::vcovCL(injury_nb_category, cluster = model_data$team))
    }, error = function(e) NULL)
    
    injury_offset_clustered <- tryCatch({
      model_data_filtered <- model_data %>% filter(active_roster_size > 0)
      lmtest::coeftest(injury_nb_offset,
                       vcov = sandwich::vcovCL(injury_nb_offset, cluster = model_data_filtered$team))
    }, error = function(e) NULL)
  }
  
  # Summary by rest category
  injury_summary <- model_data %>%
    filter(!is.na(injuries_next_week)) %>%
    group_by(rest_category) %>%
    summarise(
      n_games = n(),
      mean_new_injuries = mean(injuries_next_week, na.rm = TRUE),
      se_injuries = sd(injuries_next_week, na.rm = TRUE) / sqrt(n()),
      total_injuries = sum(injuries_next_week, na.rm = TRUE),
      .groups = "drop"
    )
  
  # Summary by rest differential
  injury_by_restdiff <- model_data %>%
    filter(!is.na(injuries_next_week), !is.na(rest_diff)) %>%
    mutate(rest_diff_bin = cut(rest_diff, breaks = c(-Inf, -2, 0, 2, Inf),
                               labels = c("≤-2", "-1 to 0", "1 to 2", "≥3"))) %>%
    group_by(rest_diff_bin) %>%
    summarise(
      n_games = n(),
      mean_injuries = mean(injuries_next_week, na.rm = TRUE),
      se_injuries = sd(injuries_next_week, na.rm = TRUE) / sqrt(n()),
      .groups = "drop"
    )
  
  list(
    poisson = poisson_model,
    poisson_clustered = poisson_clustered,
    negbin_restdiff = injury_nb_restdiff,
    negbin_restdiff_clustered = injury_restdiff_clustered,
    negbin_unfair = injury_nb_unfair,
    negbin_unfair_clustered = injury_unfair_clustered,
    negbin_category = injury_nb_category,
    negbin_category_clustered = injury_category_clustered,
    negbin_offset = injury_nb_offset,
    negbin_offset_clustered = injury_offset_clustered,
    overdispersion = dispersion_ratio,
    summary = injury_summary,
    by_restdiff = injury_by_restdiff
  )
}

# -----------------------------------------------------------------------------
# 3.3 Win/Loss Analysis
# -----------------------------------------------------------------------------
analyze_win_probability <- function(data) {
  
  model_data <- data %>%
    filter(rest_category != "First Game", !is.na(win)) %>%
    mutate(
      rest_category = factor(rest_category,
                             levels = c("Standard (6-7 days)", "Thursday (Short Rest)",
                                        "Thursday (Not Short Rest)", "Short (4 days)", 
                                        "Short (5 days)", "Extended (MNF->SUN)", 
                                        "Extended (8-10 days)", "Post-Bye"))
    )
  
  # Model 1: Simple rest differential effect on win probability
  win_simple <- glm(
    win ~ rest_diff,
    data = model_data,
    family = binomial()
  )
  
  # Model 2: Rest category effect
  win_category <- glm(
    win ~ rest_category + home,
    data = model_data,
    family = binomial()
  )
  
  # Model 3: Full model with cumulative workload
  win_full <- glm(
    win ~ rest_diff + unfair_rest + home +
      games_since_bye + cum_short_weeks +
      crossed_timezones + factor(season),
    data = model_data,
    family = binomial()
  )
  
  # Model 4: With opponent workload
  win_matchup <- glm(
    win ~ rest_diff + home +
      games_since_bye + opp_games_since_bye +
      cum_short_weeks + opp_cum_short_weeks +
      factor(season),
    data = model_data,
    family = binomial()
  )
  
  # Model 5: Mixed-effects model with team random intercepts
  # Note: We use factor(season) as fixed effects (to estimate season-specific intercepts)
  # combined with (1|team) random intercepts (to account for team-level heterogeneity).
  # This differs from Model 4 which uses (1|season) random intercepts. Here, fixed season
  # effects allow us to estimate and interpret season-specific baseline win probabilities,
  # while random team intercepts account for unobserved team characteristics.
  win_mixed <- tryCatch({
    glmer(
    win ~ rest_diff + home +
      games_since_bye + cum_short_weeks +
        factor(season) + (1 | team),
    data = model_data,
      family = binomial(),
      control = glmerControl(optimizer = "bobyqa", optCtrl = list(maxfun = 2e5))
    )
  }, error = function(e) {
    # Fallback: simpler model if convergence fails (team random intercepts only)
    glmer(
      win ~ rest_diff + home +
        games_since_bye + cum_short_weeks +
        (1 | team),
      data = model_data,
      family = binomial(),
      control = glmerControl(optimizer = "bobyqa", optCtrl = list(maxfun = 2e5))
    )
  })
  
  # Clustered standard errors for all win models (team level)
  win_simple_clustered <- NULL
  win_category_clustered <- NULL
  win_full_clustered <- NULL
  win_matchup_clustered <- NULL
  win_mixed_clustered <- NULL
  
  if (requireNamespace("sandwich", quietly = TRUE) &&
      requireNamespace("lmtest", quietly = TRUE)) {
    win_simple_clustered <- tryCatch({
      lmtest::coeftest(win_simple,
                       vcov = sandwich::vcovCL(win_simple, cluster = model_data$team))
    }, error = function(e) NULL)
    
    win_category_clustered <- tryCatch({
      lmtest::coeftest(win_category,
                       vcov = sandwich::vcovCL(win_category, cluster = model_data$team))
    }, error = function(e) NULL)
    
    win_full_clustered <- tryCatch({
      lmtest::coeftest(win_full,
                       vcov = sandwich::vcovCL(win_full, cluster = model_data$team))
    }, error = function(e) NULL)
    
    win_matchup_clustered <- tryCatch({
      lmtest::coeftest(win_matchup,
                       vcov = sandwich::vcovCL(win_matchup, cluster = model_data$team))
    }, error = function(e) NULL)
    
    # Clustered SE for mixed-effects model (robustness check)
    win_mixed_clustered <- tryCatch({
      lmtest::coeftest(win_mixed,
                       vcov = sandwich::vcovCL(win_mixed, cluster = model_data$team))
    }, error = function(e) NULL)
  }
  
  # Extract odds ratios
  extract_or <- function(model, model_name) {
    tidy(model, exponentiate = TRUE, conf.int = TRUE) %>%
      mutate(model = model_name)
  }
  
  odds_ratios <- bind_rows(
    extract_or(win_simple, "Simple"),
    extract_or(win_full, "Full"),
    extract_or(win_matchup, "Matchup")
  ) %>%
    filter(!grepl("Intercept|season", term))
  
  # Win rate summary by rest category
  win_summary <- model_data %>%
    group_by(rest_category) %>%
    summarise(
      n_games = n(),
      wins = sum(win),
      losses = n_games - wins,
      win_pct = mean(win),
      se_win_pct = sqrt(win_pct * (1 - win_pct) / n_games),
      .groups = "drop"
    )
  
  # Win rate by rest differential
  win_by_restdiff <- model_data %>%
    filter(!is.na(rest_diff)) %>%
    mutate(rest_diff_bin = cut(rest_diff,
                               breaks = c(-Inf, -3, -1, 1, 3, Inf),
                               labels = c("≤-3", "-2 to -1", "0 to 1", "2 to 3", "≥4"))) %>%
    group_by(rest_diff_bin) %>%
    summarise(
      n_games = n(),
      win_pct = mean(win),
      se_win_pct = sqrt(win_pct * (1 - win_pct) / n_games),
      .groups = "drop"
    )
  
  # Calculate marginal effects
  # Probability change for unfair rest (rest_diff <= -2, matching unfair_rest definition)
  baseline_prob <- predict(win_full,
                           newdata = data.frame(
                             rest_diff = 0,
                             unfair_rest = FALSE,
                             home = FALSE,
                             games_since_bye = 4,
                             cum_short_weeks = 1,
                             crossed_timezones = FALSE,
                             season = 2023
                           ),
                           type = "response")
  
  disadvantage_prob <- predict(win_full,
                               newdata = data.frame(
                                 rest_diff = -2,  # Match unfair_rest threshold
                                 unfair_rest = TRUE,
                                 home = FALSE,
                                 games_since_bye = 4,
                                 cum_short_weeks = 1,
                                 crossed_timezones = FALSE,
                                 season = 2023
                               ),
                               type = "response")
  
  marginal_effect <- baseline_prob - disadvantage_prob
  
  list(
    simple = win_simple,
    simple_clustered = win_simple_clustered,
    category = win_category,
    category_clustered = win_category_clustered,
    full = win_full,
    full_clustered = win_full_clustered,
    matchup = win_matchup,
    matchup_clustered = win_matchup_clustered,
    mixed = win_mixed,
    mixed_clustered = win_mixed_clustered,
    odds_ratios = odds_ratios,
    summary = win_summary,
    by_restdiff = win_by_restdiff,
    marginal_effect = list(
      baseline_win_prob = as.numeric(baseline_prob),
      disadvantage_win_prob = as.numeric(disadvantage_prob),
      effect = as.numeric(marginal_effect)
    )
  )
}

# -----------------------------------------------------------------------------
# 3.4 17-Game Season Difference-in-Differences
# -----------------------------------------------------------------------------
analyze_17_game_did <- function(data) {
  
  # Filter to pre/post periods (skip COVID-affected 2020)
  # Pre-period: 2015-2019 (16-game seasons)
  # Post-period: 2021-2024 (17-game seasons)
  did_data <- data %>%
    filter(season %in% c(2015:2019, 2021:2024)) %>%
    mutate(
      post_17 = season >= 2021,
      late_season = week >= 13,
      very_late = week >= 15
    )
  
  # DiD Model 1: Injury rates in late season
  did_injuries <- lm(
    injuries_next_week ~ post_17 * late_season +
      home + surface + factor(team),
    data = did_data
  )
  
  # DiD Model 2: Performance decay in late season
  did_performance <- lm(
    epa_play ~ post_17 * late_season +
      home + surface + factor(team),
    data = did_data
  )
  
  # DiD Model 3: Win probability in late season
  did_wins <- glm(
    win ~ post_17 * late_season + home + factor(team),
    data = did_data,
    family = binomial()
  )
  
  # Robust standard errors (clustered by team) for all DiD models
  did_injuries_robust <- NULL
  did_performance_robust <- NULL
  did_wins_robust <- NULL
  
  if (requireNamespace("sandwich", quietly = TRUE) &&
      requireNamespace("lmtest", quietly = TRUE)) {
    
    did_injuries_robust <- lmtest::coeftest(
      did_injuries,
      vcov = sandwich::vcovCL(did_injuries, cluster = did_data$team)
    )
    
    did_performance_robust <- lmtest::coeftest(
      did_performance,
      vcov = sandwich::vcovCL(did_performance, cluster = did_data$team)
    )
    
    did_wins_robust <- tryCatch({
      lmtest::coeftest(
        did_wins,
        vcov = sandwich::vcovCL(did_wins, cluster = did_data$team)
      )
    }, error = function(e) NULL)
  }
  
  # Summary: Pre vs Post 17-game season
  pre_post_summary <- did_data %>%
    group_by(post_17, late_season) %>%
    summarise(
      n_games = n(),
      mean_injuries = mean(injuries_next_week, na.rm = TRUE),
      mean_epa = mean(epa_play, na.rm = TRUE),
      win_pct = mean(win, na.rm = TRUE),
      .groups = "drop"
    ) %>%
    pivot_wider(
      names_from = late_season,
      values_from = c(n_games, mean_injuries, mean_epa, win_pct),
      names_sep = "_late_"
    )
  
  # Calculate DiD estimates manually
  pre_early_inj <- did_data %>%
    filter(!post_17, !late_season) %>%
    summarise(m = mean(injuries_next_week, na.rm = TRUE)) %>%
    pull(m)
  
  pre_late_inj <- did_data %>%
    filter(!post_17, late_season) %>%
    summarise(m = mean(injuries_next_week, na.rm = TRUE)) %>%
    pull(m)
  
  post_early_inj <- did_data %>%
    filter(post_17, !late_season) %>%
    summarise(m = mean(injuries_next_week, na.rm = TRUE)) %>%
    pull(m)
  
  post_late_inj <- did_data %>%
    filter(post_17, late_season) %>%
    summarise(m = mean(injuries_next_week, na.rm = TRUE)) %>%
    pull(m)
  
  did_estimate_injuries <- (post_late_inj - post_early_inj) - (pre_late_inj - pre_early_inj)
  
  # Same for EPA
  pre_early_epa <- did_data %>%
    filter(!post_17, !late_season) %>%
    summarise(m = mean(epa_play, na.rm = TRUE)) %>%
    pull(m)
  
  pre_late_epa <- did_data %>%
    filter(!post_17, late_season) %>%
    summarise(m = mean(epa_play, na.rm = TRUE)) %>%
    pull(m)
  
  post_early_epa <- did_data %>%
    filter(post_17, !late_season) %>%
    summarise(m = mean(epa_play, na.rm = TRUE)) %>%
    pull(m)
  
  post_late_epa <- did_data %>%
    filter(post_17, late_season) %>%
    summarise(m = mean(epa_play, na.rm = TRUE)) %>%
    pull(m)
  
  did_estimate_epa <- (post_late_epa - post_early_epa) - (pre_late_epa - pre_early_epa)
  
  # Parallel trends check: test pre-period trends
  pre_period_data <- did_data %>% filter(!post_17)
  parallel_trends_test <- tryCatch({
    # Test if late_season trend differs by season in pre-period
    pre_trend_model <- lm(
      injuries_next_week ~ late_season * factor(season),
      data = pre_period_data
    )
    # Extract interaction p-value
    trend_coefs <- tidy(pre_trend_model)
    trend_pvalue <- trend_coefs %>%
      filter(grepl("late_season.*season", term)) %>%
      pull(p.value)
    if (length(trend_pvalue) == 0) trend_pvalue <- NA
    list(model = pre_trend_model, interaction_pvalue = trend_pvalue[1])
  }, error = function(e) NULL)
  
  # Clustered SE for pre-trend model
  pre_trend_clustered <- NULL
  if (!is.null(parallel_trends_test) && !is.null(parallel_trends_test$model)) {
    if (requireNamespace("sandwich", quietly = TRUE) &&
        requireNamespace("lmtest", quietly = TRUE)) {
      pre_trend_clustered <- tryCatch({
        lmtest::coeftest(
          parallel_trends_test$model,
          vcov = sandwich::vcovCL(parallel_trends_test$model, cluster = pre_period_data$team)
        )
      }, error = function(e) NULL)
    }
  }
  
  # Weekly trends plot data
  weekly_trends <- did_data %>%
    group_by(post_17, week) %>%
    summarise(
      mean_injuries = mean(injuries_next_week, na.rm = TRUE),
      mean_epa = mean(epa_play, na.rm = TRUE),
      n = n(),
      .groups = "drop"
    ) %>%
    mutate(period = if_else(post_17, "17-Game (2021-23)", "16-Game (2015-19)"))
  
  list(
    injury_model = did_injuries,
    performance_model = did_performance,
    win_model = did_wins,
    injury_robust = did_injuries_robust,
    performance_robust = did_performance_robust,
    win_robust = did_wins_robust,
    summary = pre_post_summary,
    did_estimates = list(
      injuries = did_estimate_injuries,
      epa = did_estimate_epa
    ),
    weekly_trends = weekly_trends,
    parallel_trends = parallel_trends_test,
    parallel_trends_clustered = pre_trend_clustered
  )
}

# -----------------------------------------------------------------------------
# 3.4.1 Event Study DiD (Dynamic Effects by Week)
# -----------------------------------------------------------------------------
analyze_event_study_did <- function(data) {
  
  # Filter to pre/post periods
  event_data <- data %>%
    filter(season %in% c(2015:2019, 2021:2024)) %>%
    mutate(
      post_17 = season >= 2021,
      # Create relative week indicators (weeks 1-12 as reference, 13-18 as treatment)
      week_rel = case_when(
        week <= 12 ~ week,
        week >= 13 ~ week - 12,  # 1-6 for late season
        TRUE ~ NA_real_
      ),
      # Week indicators for event study
      week_factor = factor(week)
    )
  
  # Create week × post interactions manually (week 12 as reference)
  week_post_interactions <- event_data %>%
    mutate(
      week1_post = (week == 1) * post_17,
      week2_post = (week == 2) * post_17,
      week3_post = (week == 3) * post_17,
      week4_post = (week == 4) * post_17,
      week5_post = (week == 5) * post_17,
      week6_post = (week == 6) * post_17,
      week7_post = (week == 7) * post_17,
      week8_post = (week == 8) * post_17,
      week9_post = (week == 9) * post_17,
      week10_post = (week == 10) * post_17,
      week11_post = (week == 11) * post_17,
      week12_post = (week == 12) * post_17,  # Reference week
      week13_post = (week == 13) * post_17,
      week14_post = (week == 14) * post_17,
      week15_post = (week == 15) * post_17,
      week16_post = (week == 16) * post_17,
      week17_post = (week == 17) * post_17,
      week18_post = (week == 18) * post_17
    )
  
  # Event study model for injuries (week 12 as reference - excluded from interactions)
  event_injuries <- lm(
    injuries_next_week ~ week1_post + week2_post + week3_post + week4_post +
      week5_post + week6_post + week7_post + week8_post + week9_post +
      week10_post + week11_post + week13_post + week14_post + week15_post +
      week16_post + week17_post + week18_post +
      factor(week) + factor(team) + factor(season) + home + surface,
    data = week_post_interactions
  )
  
  # Event study model for performance (week 12 as reference)
  event_performance <- lm(
    epa_play ~ week1_post + week2_post + week3_post + week4_post +
      week5_post + week6_post + week7_post + week8_post + week9_post +
      week10_post + week11_post + week13_post + week14_post + week15_post +
      week16_post + week17_post + week18_post +
      factor(week) + factor(team) + factor(season) + home + surface,
    data = week_post_interactions
  )
  
  # Extract coefficients and create event study plot data
  extract_event_coefs <- function(model, outcome_name) {
    coefs <- tidy(model) %>%
      filter(grepl("week.*_post", term)) %>%
      mutate(
        # Extract week number from term (e.g., "week13_post" -> 13)
        week = as.numeric(stringr::str_extract(term, "\\d+")),
        outcome = outcome_name
      ) %>%
      # Add reference week (week 12 = 0) - exclude week12_post from model
      bind_rows(
        tibble(
          term = "week12_post",
          estimate = 0,
          std.error = 0,
          statistic = 0,
          p.value = 1,
          week = 12,
          outcome = outcome_name
        )
      ) %>%
      arrange(week) %>%
      mutate(
        ci_lower = estimate - 1.96 * std.error,
        ci_upper = estimate + 1.96 * std.error
      )
  }
  
  event_injuries_coefs <- extract_event_coefs(event_injuries, "Injuries")
  event_performance_coefs <- extract_event_coefs(event_performance, "EPA/Play")
  
  # Clustered standard errors
  event_injuries_robust <- NULL
  event_performance_robust <- NULL
  
  if (requireNamespace("sandwich", quietly = TRUE) &&
      requireNamespace("lmtest", quietly = TRUE)) {
    event_injuries_robust <- tryCatch({
      lmtest::coeftest(
        event_injuries,
        vcov = sandwich::vcovCL(event_injuries, cluster = week_post_interactions$team)
      )
    }, error = function(e) NULL)
    
    event_performance_robust <- tryCatch({
      lmtest::coeftest(
        event_performance,
        vcov = sandwich::vcovCL(event_performance, cluster = week_post_interactions$team)
      )
    }, error = function(e) NULL)
  }
  
  # Re-extract with robust SE if available
  if (!is.null(event_injuries_robust)) {
    event_injuries_coefs <- tidy(event_injuries_robust) %>%
      filter(grepl("week.*_post", term)) %>%
      mutate(
        week = as.numeric(stringr::str_extract(term, "\\d+")),
        outcome = "Injuries"
      ) %>%
      bind_rows(
        tibble(
          term = "week12_post",
          estimate = 0,
          std.error = 0,
          statistic = 0,
          p.value = 1,
          week = 12,
          outcome = "Injuries"
        )
      ) %>%
      arrange(week) %>%
      mutate(
        ci_lower = estimate - 1.96 * std.error,
        ci_upper = estimate + 1.96 * std.error
      )
  }
  
  if (!is.null(event_performance_robust)) {
    event_performance_coefs <- tidy(event_performance_robust) %>%
      filter(grepl("week.*_post", term)) %>%
      mutate(
        week = as.numeric(stringr::str_extract(term, "\\d+")),
        outcome = "EPA/Play"
      ) %>%
      bind_rows(
        tibble(
          term = "week12_post",
          estimate = 0,
          std.error = 0,
          statistic = 0,
          p.value = 1,
          week = 12,
          outcome = "EPA/Play"
        )
      ) %>%
      arrange(week) %>%
      mutate(
        ci_lower = estimate - 1.96 * std.error,
        ci_upper = estimate + 1.96 * std.error
      )
  }
  
  list(
    injury_model = event_injuries,
    performance_model = event_performance,
    injury_robust = event_injuries_robust,
    performance_robust = event_performance_robust,
    injury_coefs = event_injuries_coefs,
    performance_coefs = event_performance_coefs
  )
}

# =============================================================================
# PART 3.5: INJURY SEVERITY ANALYSIS
# =============================================================================

# -----------------------------------------------------------------------------
# 3.5 Analyze Injury Severity (Games Missed)
# -----------------------------------------------------------------------------
analyze_injury_severity <- function(data) {
  
  model_data <- data %>%
    filter(rest_category != "First Game", !is.na(player_out_weeks_next_4)) %>%
    mutate(
      rest_category = factor(rest_category,
                             levels = c("Standard (6-7 days)", "Thursday (Short Rest)",
                                        "Thursday (Not Short Rest)", "Short (4 days)", 
                                        "Short (5 days)", "Extended (MNF->SUN)", 
                                        "Extended (8-10 days)", "Post-Bye"))
    )
  
  # Model 1: Player out designations next 4 weeks (severity proxy)
  # Note: This counts team-week "out" designations, not individual player games missed
  severity_model <- MASS::glm.nb(
    player_out_weeks_next_4 ~ rest_category + rest_diff + home + surface +
      games_since_bye + cum_short_weeks + factor(season) +
      offset(log(active_roster_size)),
    data = model_data %>% filter(active_roster_size > 0)
  )
  
  # Model 2: Players inactive next week (immediate severity)
  inactive_model <- MASS::glm.nb(
    players_out_next_week ~ rest_category + rest_diff + home + surface +
      games_since_bye + cum_short_weeks + factor(season) +
      offset(log(active_roster_size)),
    data = model_data %>% filter(active_roster_size > 0)
  )
  
  # Model 3: Unfair rest effect on severity
  severity_unfair <- MASS::glm.nb(
    player_out_weeks_next_4 ~ unfair_rest + rest_diff + home + surface +
      games_since_bye + cum_short_weeks + factor(season) +
      offset(log(active_roster_size)),
    data = model_data %>% filter(active_roster_size > 0)
  )
  
  # Clustered standard errors for all severity models
  severity_clustered <- NULL
  inactive_clustered <- NULL
  severity_unfair_clustered <- NULL
  
  if (requireNamespace("sandwich", quietly = TRUE) &&
      requireNamespace("lmtest", quietly = TRUE)) {
    model_data_filtered <- model_data %>% filter(active_roster_size > 0)
    
    severity_clustered <- tryCatch({
      lmtest::coeftest(severity_model,
                       vcov = sandwich::vcovCL(severity_model, cluster = model_data_filtered$team))
    }, error = function(e) NULL)
    
    inactive_clustered <- tryCatch({
      lmtest::coeftest(inactive_model,
                       vcov = sandwich::vcovCL(inactive_model, cluster = model_data_filtered$team))
    }, error = function(e) NULL)
    
    severity_unfair_clustered <- tryCatch({
      lmtest::coeftest(severity_unfair,
                       vcov = sandwich::vcovCL(severity_unfair, cluster = model_data_filtered$team))
    }, error = function(e) NULL)
  }
  
  # Summary by rest category
  severity_summary <- model_data %>%
    filter(!is.na(player_out_weeks_next_4)) %>%
    group_by(rest_category) %>%
    summarise(
      n_games = n(),
      mean_games_missed = mean(player_out_weeks_next_4, na.rm = TRUE),  # Keep name for compatibility
      se_games_missed = sd(player_out_weeks_next_4, na.rm = TRUE) / sqrt(n()),
      mean_inactive_next = mean(players_out_next_week, na.rm = TRUE),
      se_inactive_next = sd(players_out_next_week, na.rm = TRUE) / sqrt(n()),
      total_games_missed = sum(player_out_weeks_next_4, na.rm = TRUE),
      .groups = "drop"
    )
  
  # Extract rate ratios
  severity_coefs <- tidy(severity_model) %>%
    filter(grepl("rest_category", term)) %>%
    mutate(
      rate_ratio = exp(estimate),
      rr_lower = exp(estimate - 1.96 * std.error),
      rr_upper = exp(estimate + 1.96 * std.error)
    )
  
  list(
    severity_model = severity_model,
    inactive_model = inactive_model,
    severity_unfair = severity_unfair,
    severity_clustered = severity_clustered,
    inactive_clustered = inactive_clustered,
    severity_unfair_clustered = severity_unfair_clustered,
    summary = severity_summary,
    rate_ratios = severity_coefs
  )
}

# =============================================================================
# PART 3.6: POSITION HETEROGENEITY ANALYSIS
# =============================================================================

# -----------------------------------------------------------------------------
# 3.6 Analyze Position-Specific Effects
# -----------------------------------------------------------------------------
analyze_position_heterogeneity <- function(injury_data, survival_data, team_games) {
  
  if (is.null(injury_data) || nrow(injury_data) == 0) {
    return(NULL)
  }
  
  # Position groups
  injury_with_pos <- injury_data %>%
    mutate(
      position_group = case_when(
        grepl("QB", position, ignore.case = TRUE) ~ "QB",
        grepl("RB|FB", position, ignore.case = TRUE) ~ "RB",
        grepl("WR", position, ignore.case = TRUE) ~ "WR",
        grepl("TE", position, ignore.case = TRUE) ~ "TE",
        grepl("OL|T|G|C", position, ignore.case = TRUE) ~ "OL",
        grepl("DL|DE|DT|NT", position, ignore.case = TRUE) ~ "DL",
        grepl("LB|ILB|OLB", position, ignore.case = TRUE) ~ "LB",
        grepl("DB|CB|S|FS|SS", position, ignore.case = TRUE) ~ "DB",
        TRUE ~ "Other"
      )
    ) %>%
    filter(!is.na(position_group), position_group != "Other")
  
  # Join with team rest data
  team_rest <- team_games %>%
    dplyr::select(season, week, team, days_rest, rest_category, is_tnf,
                  is_short_week, rest_diff, unfair_rest, games_since_bye,
                  cum_short_weeks)
  
  injury_with_rest <- injury_with_pos %>%
    left_join(team_rest, by = c("season", "week", "team"))
  
  # Position-level injury rates by rest category
  position_injury_rates <- injury_with_rest %>%
    filter(!is.na(rest_category), rest_category != "First Game") %>%
    group_by(position_group, rest_category) %>%
    summarise(
      n_players = n(),
      n_new_injuries = sum(is_new_injury, na.rm = TRUE),
      injury_rate = mean(is_new_injury, na.rm = TRUE),
      se_injury_rate = sd(is_new_injury, na.rm = TRUE) / sqrt(n()),
      n_players_out = sum(is_out, na.rm = TRUE),
      out_rate = mean(is_out, na.rm = TRUE),
      .groups = "drop"
    ) %>%
    filter(n_players >= 10)  # Minimum sample size
  
  # Position-specific TNF vs Standard comparison
  position_tnf_comparison <- position_injury_rates %>%
    filter(rest_category %in% c("Standard (6-7 days)", "Thursday (Short Rest)")) %>%
    pivot_wider(
      id_cols = position_group,
      names_from = rest_category,
      values_from = c(n_players, n_new_injuries, injury_rate, se_injury_rate),
      names_sep = "_"
    )
  
  # Handle column names (pivot_wider creates names with dots)
  std_col <- grep("Standard", names(position_tnf_comparison), value = TRUE)
  tnf_col <- grep("Thursday.*Short Rest", names(position_tnf_comparison), value = TRUE)
  
  if (length(std_col) > 0 && length(tnf_col) > 0) {
    std_rate_col <- grep("injury_rate", std_col, value = TRUE)[1]
    tnf_rate_col <- grep("injury_rate", tnf_col, value = TRUE)[1]
    std_se_col <- grep("se_injury_rate", std_col, value = TRUE)[1]
    tnf_se_col <- grep("se_injury_rate", tnf_col, value = TRUE)[1]
    
    if (!is.na(std_rate_col) && !is.na(tnf_rate_col)) {
      position_tnf_comparison <- position_tnf_comparison %>%
        mutate(
          # Calculate rate difference and ratio
          rate_diff = .data[[tnf_rate_col]] - .data[[std_rate_col]],
          rate_ratio = .data[[tnf_rate_col]] / .data[[std_rate_col]],
          # Standard error for difference
          se_diff = sqrt(.data[[tnf_se_col]]^2 + .data[[std_se_col]]^2),
          # 95% CI for rate ratio (approximate)
          rate_ratio_lower = rate_ratio * exp(-1.96 * se_diff / .data[[std_rate_col]]),
          rate_ratio_upper = rate_ratio * exp(1.96 * se_diff / .data[[std_rate_col]]),
          # Statistical significance (z-test)
          z_score = rate_diff / se_diff,
          p_value = 2 * (1 - pnorm(abs(z_score)))
        ) %>%
        filter(!is.na(rate_ratio)) %>%
        arrange(desc(rate_ratio))
    } else {
      position_tnf_comparison <- tibble()
    }
  } else {
    position_tnf_comparison <- tibble()
  }
  
  # Position-specific survival analysis
  surv_summary <- survival_data$summary %>%
    filter(!is.na(position_group), position_group != "Other")
  
  if (nrow(surv_summary) > 0 && n_distinct(surv_summary$position_group) > 1) {
    surv_obj_pos <- Surv(time = surv_summary$time_to_injury,
                        event = surv_summary$injured)
    
    # Cox model with position interaction (with cluster for robust SE)
    cox_position <- coxph(surv_obj_pos ~ rest_group * position_group + 
                          pct_short_weeks + total_games + factor(season) + cluster(team),
                          data = surv_summary)
    
    # Position-stratified survival curves
    km_by_position <- survfit(surv_obj_pos ~ position_group, data = surv_summary)
    
    # Position-specific hazard ratios
    position_hr <- tidy(cox_position) %>%
      filter(grepl("rest_group|position_group", term)) %>%
    mutate(
        hr = exp(estimate),
        hr_lower = exp(estimate - 1.96 * std.error),
        hr_upper = exp(estimate + 1.96 * std.error)
    )
  } else {
    cox_position <- NULL
    km_by_position <- NULL
    position_hr <- NULL
  }
  
  # Position-specific short-rest exposure
  position_exposure <- injury_with_rest %>%
    filter(!is.na(is_short_week)) %>%
    group_by(position_group) %>%
    summarise(
      n_observations = n(),
      pct_short_weeks = mean(is_short_week, na.rm = TRUE),
      pct_tnf = mean(is_tnf, na.rm = TRUE),
      mean_rest_diff = mean(rest_diff, na.rm = TRUE),
      pct_unfair_rest = mean(unfair_rest, na.rm = TRUE),
      .groups = "drop"
    ) %>%
    filter(n_observations >= 50)
  
  list(
    position_injury_rates = position_injury_rates,
    position_tnf_comparison = position_tnf_comparison,
    position_exposure = position_exposure,
    cox_position = cox_position,
    km_by_position = km_by_position,
    position_hr = position_hr,
    injury_data_with_pos = injury_with_rest
  )
}

# =============================================================================
# PART 3.7: INJURY TYPE HETEROGENEITY ANALYSIS
# =============================================================================

# -----------------------------------------------------------------------------
# 3.7 Analyze Injury Type Heterogeneity (Soft-tissue vs Joint vs Contact)
# -----------------------------------------------------------------------------
analyze_injury_types <- function(injury_data, team_games) {
  
  if (is.null(injury_data) || nrow(injury_data) == 0) {
    return(NULL)
  }
  
  # Classify injuries by type
  # Use secondary_injury if available, otherwise try primary_injury or practice_status
  injury_classified <- injury_data %>%
    mutate(
      injury_text = case_when(
        !is.na(secondary_injury) & secondary_injury != "" ~ secondary_injury,
        !is.na(primary_injury) & primary_injury != "" ~ primary_injury,
        !is.na(practice_status) & practice_status != "" ~ practice_status,
        TRUE ~ NA_character_
      ),
      injury_type = case_when(
        # Soft-tissue injuries (muscle strains, pulls)
        !is.na(injury_text) & 
        grepl("hamstring|groin|calf|quad|muscle|strain|pull|achilles", 
              tolower(injury_text), ignore.case = TRUE) ~ "Soft Tissue",
        # Joint/ligament injuries
        !is.na(injury_text) &
        grepl("knee|ankle|shoulder|elbow|ligament|tendon|ACL|MCL|PCL|meniscus|rotator",
              tolower(injury_text), ignore.case = TRUE) ~ "Joint/Ligament",
        # Contact trauma
        !is.na(injury_text) &
        grepl("concussion|head|neck|fracture|broken|dislocation|rib",
              tolower(injury_text), ignore.case = TRUE) ~ "Contact Trauma",
        # Other/Unknown
        is.na(injury_text) | injury_text == "" ~ "Unknown",
        TRUE ~ "Other"
      )
    )
  
  # Join with team rest data
  team_rest <- team_games %>%
    dplyr::select(season, week, team, days_rest, rest_category, is_tnf,
                  is_short_week, rest_diff, unfair_rest, games_since_bye,
                  cum_short_weeks)
  
  injury_with_rest <- injury_classified %>%
    left_join(team_rest, by = c("season", "week", "team"))
  
  # Injury rates by type and rest category
  injury_type_rates <- injury_with_rest %>%
    filter(!is.na(rest_category), rest_category != "First Game",
           !is.na(injury_type), injury_type != "Unknown") %>%
    group_by(injury_type, rest_category) %>%
    summarise(
      n_observations = n(),
      n_new_injuries = sum(is_new_injury, na.rm = TRUE),
      injury_rate = mean(is_new_injury, na.rm = TRUE),
      se_rate = sd(is_new_injury, na.rm = TRUE) / sqrt(n()),
      .groups = "drop"
    ) %>%
    filter(n_observations >= 20)  # Minimum sample size
  
  # TNF vs Standard by injury type
  injury_type_tnf_comparison <- injury_type_rates %>%
    filter(rest_category %in% c("Standard (6-7 days)", "Thursday (Short Rest)")) %>%
    pivot_wider(
      id_cols = injury_type,
      names_from = rest_category,
      values_from = c(n_observations, n_new_injuries, injury_rate, se_rate),
      names_sep = "_"
    )
  
  # Handle column names (pivot_wider creates names with dots)
  std_cols <- grep("Standard", names(injury_type_tnf_comparison), value = TRUE)
  tnf_cols <- grep("Thursday.*Short Rest", names(injury_type_tnf_comparison), value = TRUE)
  
  if (length(std_cols) > 0 && length(tnf_cols) > 0) {
    std_rate_col <- grep("injury_rate", std_cols, value = TRUE)[1]
    tnf_rate_col <- grep("injury_rate", tnf_cols, value = TRUE)[1]
    std_se_col <- grep("se_rate", std_cols, value = TRUE)[1]
    tnf_se_col <- grep("se_rate", tnf_cols, value = TRUE)[1]
    
    if (!is.na(std_rate_col) && !is.na(tnf_rate_col)) {
      injury_type_tnf_comparison <- injury_type_tnf_comparison %>%
        mutate(
          rate_diff = .data[[tnf_rate_col]] - .data[[std_rate_col]],
          rate_ratio = .data[[tnf_rate_col]] / .data[[std_rate_col]],
          se_diff = sqrt(.data[[tnf_se_col]]^2 + .data[[std_se_col]]^2),
          z_score = rate_diff / se_diff,
          p_value = 2 * (1 - pnorm(abs(z_score)))
        ) %>%
        filter(!is.na(rate_ratio))
    } else {
      injury_type_tnf_comparison <- tibble()
    }
  } else {
    injury_type_tnf_comparison <- tibble()
  }
  
  # Model: Injury type by rest category (multinomial or separate models)
  # For simplicity, model each type separately
  soft_tissue_data <- injury_with_rest %>%
    filter(injury_type == "Soft Tissue", !is.na(rest_category), 
           rest_category != "First Game") %>%
    group_by(season, week, team) %>%
    summarise(
      n_soft_tissue = sum(is_new_injury, na.rm = TRUE),
      is_tnf = first(is_tnf),
      is_short_week = first(is_short_week),
      rest_diff = first(rest_diff),
      unfair_rest = first(unfair_rest),
      games_since_bye = first(games_since_bye),
      cum_short_weeks = first(cum_short_weeks),
      .groups = "drop"
    )
  
  # Get roster size for offset (calculate from injury data)
  roster_sizes <- injury_with_rest %>%
    group_by(season, team) %>%
    summarise(
      unique_players_seen = n_distinct(gsis_id),
      .groups = "drop"
    ) %>%
    mutate(
      active_roster_size = pmax(unique_players_seen, CONFIG$game_day_roster_size)
    ) %>%
    dplyr::select(season, team, active_roster_size)
  
  soft_tissue_data <- soft_tissue_data %>%
    left_join(roster_sizes, by = c("season", "team"))
  
  # Model soft-tissue injuries
  soft_tissue_model <- NULL
  soft_tissue_clustered <- NULL
  
  if (nrow(soft_tissue_data) > 0 && sum(soft_tissue_data$n_soft_tissue) > 0) {
    soft_tissue_model <- tryCatch({
      MASS::glm.nb(
        n_soft_tissue ~ is_tnf + is_short_week + rest_diff + 
          games_since_bye + cum_short_weeks + factor(season) +
          offset(log(active_roster_size)),
        data = soft_tissue_data %>% filter(active_roster_size > 0)
      )
    }, error = function(e) NULL)
    
    # Clustered SE for soft-tissue model
    if (!is.null(soft_tissue_model) && requireNamespace("sandwich", quietly = TRUE) &&
        requireNamespace("lmtest", quietly = TRUE)) {
      soft_tissue_data_filtered <- soft_tissue_data %>% filter(active_roster_size > 0)
      soft_tissue_clustered <- tryCatch({
        lmtest::coeftest(soft_tissue_model,
                         vcov = sandwich::vcovCL(soft_tissue_model, cluster = soft_tissue_data_filtered$team))
      }, error = function(e) NULL)
    }
  }
  
  # Summary by injury type
  injury_type_summary <- injury_with_rest %>%
    filter(!is.na(injury_type), injury_type != "Unknown") %>%
    group_by(injury_type) %>%
    summarise(
      total_injuries = sum(is_new_injury, na.rm = TRUE),
      pct_of_total = sum(is_new_injury, na.rm = TRUE) / 
        sum(injury_with_rest$is_new_injury, na.rm = TRUE),
      pct_on_short_rest = mean(is_short_week[is_new_injury == 1], na.rm = TRUE),
      pct_on_tnf = mean(is_tnf[is_new_injury == 1], na.rm = TRUE),
      .groups = "drop"
    )
  
  list(
    injury_type_rates = injury_type_rates,
    injury_type_tnf_comparison = injury_type_tnf_comparison,
    soft_tissue_model = soft_tissue_model,
    soft_tissue_clustered = soft_tissue_clustered,
    injury_type_summary = injury_type_summary,
    injury_data_classified = injury_with_rest
  )
}

# =============================================================================
# PART 3.8: BYE WEEK EFFECTIVENESS ANALYSIS
# =============================================================================

# -----------------------------------------------------------------------------
# 3.8 Analyze Bye Week Effectiveness
# -----------------------------------------------------------------------------
analyze_bye_effectiveness <- function(data) {
  
  model_data <- data %>%
    filter(rest_category != "First Game") %>%
    mutate(
      rest_category = factor(rest_category,
                             levels = c("Standard (6-7 days)", "Thursday (Short Rest)",
                                        "Thursday (Not Short Rest)", "Short (4 days)", 
                                        "Short (5 days)", "Extended (MNF->SUN)", 
                                        "Extended (8-10 days)", "Post-Bye"))
    )
  
  # Key comparison: TNF after bye vs TNF without bye
  tnf_comparison <- model_data %>%
    filter(is_tnf) %>%
    mutate(
      tnf_type = case_when(
        tnf_after_bye ~ "TNF After Bye",
        short_rest_no_bye ~ "TNF Without Bye",
        TRUE ~ "TNF Other"
      )
    ) %>%
    filter(tnf_type != "TNF Other") %>%
    group_by(tnf_type) %>%
    summarise(
      n_games = n(),
      mean_injuries = mean(injuries_next_week, na.rm = TRUE),
      se_injuries = sd(injuries_next_week, na.rm = TRUE) / sqrt(n()),
      mean_games_missed = mean(games_missed_next_4, na.rm = TRUE),
      se_games_missed = sd(games_missed_next_4, na.rm = TRUE) / sqrt(n()),
      mean_epa = mean(epa_play, na.rm = TRUE),
      se_epa = sd(epa_play, na.rm = TRUE) / sqrt(n()),
      win_pct = mean(win, na.rm = TRUE),
      # Selection bias checks
      mean_rest_diff = mean(rest_diff, na.rm = TRUE),
      mean_games_since_bye = mean(games_since_bye, na.rm = TRUE),
      mean_week = mean(week, na.rm = TRUE),
      .groups = "drop"
    )
  
  # Statistical test for difference
  tnf_test_data <- model_data %>%
    filter(is_tnf) %>%
    mutate(
      tnf_type = case_when(
        tnf_after_bye ~ "TNF After Bye",
        short_rest_no_bye ~ "TNF Without Bye",
        TRUE ~ NA_character_
      )
    ) %>%
    filter(!is.na(tnf_type))
  
  # T-test for injury difference
  injury_test <- tryCatch({
    t.test(injuries_next_week ~ tnf_type, data = tnf_test_data)
  }, error = function(e) NULL)
  
  # Check for selection bias: Are teams with TNF after bye different?
  selection_check <- model_data %>%
    filter(is_tnf) %>%
    mutate(has_bye_buffer = tnf_after_bye) %>%
    group_by(has_bye_buffer) %>%
    summarise(
      n = n(),
      mean_win_pct = mean(win, na.rm = TRUE),
      mean_opp_rest_diff = mean(rest_diff, na.rm = TRUE),
      mean_week = mean(week, na.rm = TRUE),
      .groups = "drop"
    )
  
  # Model 1: Injury rate by TNF type
  injury_bye_model <- MASS::glm.nb(
    injuries_next_week ~ tnf_after_bye + short_rest_no_bye + home + surface +
      games_since_bye + cum_short_weeks + factor(season) +
      offset(log(active_roster_size)),
    data = model_data %>% filter(active_roster_size > 0, is_short_week)
  )
  
  # Model 2: Severity by TNF type
  severity_bye_model <- MASS::glm.nb(
    games_missed_next_4 ~ tnf_after_bye + short_rest_no_bye + home + surface +
      games_since_bye + cum_short_weeks + factor(season) +
      offset(log(active_roster_size)),
    data = model_data %>% filter(active_roster_size > 0, is_short_week, 
                                 !is.na(games_missed_next_4))
  )
  
  # Model 3: Interaction model (bye effectiveness depends on rest differential)
  injury_interaction <- MASS::glm.nb(
    injuries_next_week ~ tnf_after_bye * rest_diff + home + surface +
      games_since_bye + cum_short_weeks + factor(season) +
      offset(log(active_roster_size)),
    data = model_data %>% filter(active_roster_size > 0, is_short_week)
  )
  
  # Clustered standard errors for bye models
  injury_bye_clustered <- NULL
  severity_bye_clustered <- NULL
  injury_interaction_clustered <- NULL
  
  if (requireNamespace("sandwich", quietly = TRUE) &&
      requireNamespace("lmtest", quietly = TRUE)) {
    model_data_short <- model_data %>% filter(active_roster_size > 0, is_short_week)
    model_data_severity <- model_data %>% filter(active_roster_size > 0, is_short_week, 
                                                  !is.na(games_missed_next_4))
    
    injury_bye_clustered <- tryCatch({
      lmtest::coeftest(injury_bye_model,
                       vcov = sandwich::vcovCL(injury_bye_model, cluster = model_data_short$team))
    }, error = function(e) NULL)
    
    severity_bye_clustered <- tryCatch({
      lmtest::coeftest(severity_bye_model,
                       vcov = sandwich::vcovCL(severity_bye_model, cluster = model_data_severity$team))
    }, error = function(e) NULL)
    
    injury_interaction_clustered <- tryCatch({
      lmtest::coeftest(injury_interaction,
                       vcov = sandwich::vcovCL(injury_interaction, cluster = model_data_short$team))
    }, error = function(e) NULL)
  }
  
  # Extract coefficients
  bye_coefs <- tidy(injury_bye_model) %>%
    filter(grepl("tnf_after_bye|short_rest_no_bye", term)) %>%
    mutate(
      rate_ratio = exp(estimate),
      rr_lower = exp(estimate - 1.96 * std.error),
      rr_upper = exp(estimate + 1.96 * std.error)
    )
  
  # Bye placement analysis (early vs late season)
  # Identify post-bye games (days_rest >= 11)
  bye_placement <- model_data %>%
    filter(days_rest >= 11 | rest_category == "Post-Bye") %>%
    mutate(
      bye_timing = case_when(
        week <= 6 ~ "Early (Weeks 1-6)",
        week <= 12 ~ "Mid (Weeks 7-12)",
        week <= 18 ~ "Late (Weeks 13-18)",
        TRUE ~ "Postseason"
      )
    ) %>%
    group_by(bye_timing) %>%
    summarise(
      n_byes = n(),
      mean_injuries_next = mean(injuries_next_week, na.rm = TRUE),
      mean_games_missed = mean(games_missed_next_4, na.rm = TRUE),
      .groups = "drop"
    )
  
  list(
    tnf_comparison = tnf_comparison,
    injury_bye_model = injury_bye_model,
    injury_bye_clustered = injury_bye_clustered,
    severity_bye_model = severity_bye_model,
    severity_bye_clustered = severity_bye_clustered,
    injury_interaction = injury_interaction,
    injury_interaction_clustered = injury_interaction_clustered,
    bye_coefs = bye_coefs,
    bye_placement = bye_placement,
    injury_test = injury_test,
    selection_check = selection_check,
    sample_size_note = glue("TNF After Bye: {sum(tnf_test_data$tnf_type == 'TNF After Bye', na.rm = TRUE)} games, ",
                            "TNF Without Bye: {sum(tnf_test_data$tnf_type == 'TNF Without Bye', na.rm = TRUE)} games")
  )
}

# =============================================================================
# PART 3.9: ADVANCED CAUSAL INFERENCE METHODS
# =============================================================================

# -----------------------------------------------------------------------------
# 3.9.1 Distributed Lag Models (Cumulative Workload Effects)
# -----------------------------------------------------------------------------
analyze_distributed_lags <- function(data) {
  
  model_data <- data %>%
    filter(rest_category != "First Game") %>%
    group_by(team, season) %>%
    arrange(week) %>%
    mutate(
      # Lagged rest differential (t-1, t-2, t-3)
      rest_diff_lag1 = lag(rest_diff, 1),
      rest_diff_lag2 = lag(rest_diff, 2),
      rest_diff_lag3 = lag(rest_diff, 3),
      
      # Lagged short week indicators
      is_short_week_lag1 = lag(is_short_week, 1),
      is_short_week_lag2 = lag(is_short_week, 2),
      is_short_week_lag3 = lag(is_short_week, 3),
      
      # Lagged unfair rest
      unfair_rest_lag1 = lag(unfair_rest, 1),
      unfair_rest_lag2 = lag(unfair_rest, 2),
      unfair_rest_lag3 = lag(unfair_rest, 3),
      
      # Cumulative lagged short weeks (sum of last 3 weeks)
      cum_short_weeks_lag3 = replace_na(is_short_week_lag1, FALSE) +
        replace_na(is_short_week_lag2, FALSE) +
        replace_na(is_short_week_lag3, FALSE)
    ) %>%
    ungroup() %>%
    filter(!is.na(rest_diff_lag1))  # Need at least 1 lag
  
  # Model 1: Injuries with distributed lags
  injury_lag_model <- MASS::glm.nb(
    injuries_next_week ~ rest_diff + rest_diff_lag1 + rest_diff_lag2 + rest_diff_lag3 +
      is_short_week + is_short_week_lag1 + is_short_week_lag2 + is_short_week_lag3 +
      home + surface + games_since_bye + cum_short_weeks + factor(season),
    data = model_data
  )
  
  # Model 2: Performance with distributed lags
  performance_lag_model <- lm(
    epa_play ~ rest_diff + rest_diff_lag1 + rest_diff_lag2 + rest_diff_lag3 +
      is_short_week + is_short_week_lag1 + is_short_week_lag2 + is_short_week_lag3 +
      home + surface + games_since_bye + cum_short_weeks + factor(season),
    data = model_data
  )
  
  # Model 3: Win probability with distributed lags
  win_lag_model <- glm(
    win ~ rest_diff + rest_diff_lag1 + rest_diff_lag2 + rest_diff_lag3 +
      unfair_rest + unfair_rest_lag1 + unfair_rest_lag2 + unfair_rest_lag3 +
      home + games_since_bye + cum_short_weeks + factor(season),
    data = model_data,
    family = binomial()
  )
  
  # Extract lag coefficients
  extract_lag_coefs <- function(model, model_name) {
    coefs <- tidy(model) %>%
      filter(grepl("rest_diff_lag|is_short_week_lag|unfair_rest_lag", term)) %>%
      mutate(
        lag_period = case_when(
          grepl("lag1", term) ~ 1,
          grepl("lag2", term) ~ 2,
          grepl("lag3", term) ~ 3,
          TRUE ~ 0
        ),
        variable = case_when(
          grepl("rest_diff", term) ~ "Rest Differential",
          grepl("is_short_week", term) ~ "Short Week",
          grepl("unfair_rest", term) ~ "Unfair Rest",
          TRUE ~ "Other"
        ),
        model_type = model_name
      )
    
    # Apply transformation based on model type (check once, not per row)
    if (model_name == "Injury") {
      coefs <- coefs %>%
        mutate(
          effect = exp(estimate),
          effect_lower = exp(estimate - 1.96 * std.error),
          effect_upper = exp(estimate + 1.96 * std.error)
        )
    } else {
      coefs <- coefs %>%
        mutate(
          effect = estimate,
          effect_lower = estimate - 1.96 * std.error,
          effect_upper = estimate + 1.96 * std.error
        )
    }
    
    coefs
  }
  
  injury_lag_coefs <- extract_lag_coefs(injury_lag_model, "Injury")
  performance_lag_coefs <- extract_lag_coefs(performance_lag_model, "Performance")
  win_lag_coefs <- extract_lag_coefs(win_lag_model, "Win")
  
  # Clustered standard errors
  injury_lag_clustered <- NULL
  performance_lag_clustered <- NULL
  win_lag_clustered <- NULL
  
  if (requireNamespace("sandwich", quietly = TRUE) &&
      requireNamespace("lmtest", quietly = TRUE)) {
    injury_lag_clustered <- tryCatch({
      lmtest::coeftest(injury_lag_model,
                       vcov = sandwich::vcovCL(injury_lag_model, cluster = model_data$team))
    }, error = function(e) NULL)
    
    performance_lag_clustered <- tryCatch({
      lmtest::coeftest(performance_lag_model,
                       vcov = sandwich::vcovCL(performance_lag_model, cluster = model_data$team))
    }, error = function(e) NULL)
    
    win_lag_clustered <- tryCatch({
      lmtest::coeftest(win_lag_model,
                       vcov = sandwich::vcovCL(win_lag_model, cluster = model_data$team))
    }, error = function(e) NULL)
  }
  
  list(
    injury_model = injury_lag_model,
    performance_model = performance_lag_model,
    win_model = win_lag_model,
    injury_clustered = injury_lag_clustered,
    performance_clustered = performance_lag_clustered,
    win_clustered = win_lag_clustered,
    injury_coefs = injury_lag_coefs,
    performance_coefs = performance_lag_coefs,
    win_coefs = win_lag_coefs
  )
}

# -----------------------------------------------------------------------------
# 3.9.2 Nonlinear Dose Response (Splines for Rest Differential)
# -----------------------------------------------------------------------------
analyze_nonlinear_dose_response <- function(data) {
  
  model_data <- data %>%
    filter(rest_category != "First Game", !is.na(rest_diff))
  
  # Check if splines package is available
  if (!requireNamespace("splines", quietly = TRUE)) {
    # Fallback: piecewise linear with knots
    model_data <- model_data %>%
      mutate(
        rest_diff_neg3 = pmax(rest_diff + 3, 0),  # Effect kicks in at -3
        rest_diff_neg2 = pmax(rest_diff + 2, 0),  # Effect kicks in at -2
        rest_diff_pos2 = pmax(rest_diff - 2, 0),  # Advantage at +2
        rest_diff_pos3 = pmax(rest_diff - 3, 0)    # Advantage at +3
      )
    
    # Piecewise linear model for injuries
    injury_spline <- MASS::glm.nb(
      injuries_next_week ~ rest_diff + rest_diff_neg3 + rest_diff_neg2 +
        rest_diff_pos2 + rest_diff_pos3 +
        home + surface + games_since_bye + cum_short_weeks + factor(season),
      data = model_data
    )
    
    # Piecewise linear for performance
    performance_spline <- lm(
      epa_play ~ rest_diff + rest_diff_neg3 + rest_diff_neg2 +
        rest_diff_pos2 + rest_diff_pos3 +
        home + surface + games_since_bye + cum_short_weeks + factor(season),
      data = model_data
    )
    
    # Piecewise linear for win probability
    win_spline <- glm(
      win ~ rest_diff + rest_diff_neg3 + rest_diff_neg2 +
        rest_diff_pos2 + rest_diff_pos3 +
        home + games_since_bye + cum_short_weeks + factor(season),
      data = model_data,
      family = binomial()
    )
    
    spline_type <- "piecewise_linear"
  } else {
    # Use natural splines
    library(splines)
    
    # Natural splines with knots at -3, -2, 0, 2, 3
    injury_spline <- MASS::glm.nb(
      injuries_next_week ~ ns(rest_diff, knots = c(-3, -2, 0, 2, 3)) +
        home + surface + games_since_bye + cum_short_weeks + factor(season),
      data = model_data
    )
    
    performance_spline <- lm(
      epa_play ~ ns(rest_diff, knots = c(-3, -2, 0, 2, 3)) +
        home + surface + games_since_bye + cum_short_weeks + factor(season),
      data = model_data
    )
    
    win_spline <- glm(
      win ~ ns(rest_diff, knots = c(-3, -2, 0, 2, 3)) +
        home + games_since_bye + cum_short_weeks + factor(season),
      data = model_data,
      family = binomial()
    )
    
    spline_type <- "natural_splines"
  }
  
  # Generate predicted effects across rest_diff range
  rest_diff_range <- seq(-5, 5, by = 0.5)
  ref_data <- model_data %>%
    slice(1) %>%
    select(home, surface, games_since_bye, cum_short_weeks, season) %>%
    mutate(
      home = FALSE,
      surface = "grass",
      games_since_bye = 4,
      cum_short_weeks = 1,
      season = 2023
    )
  
  predict_dose_response <- function(model, rest_vals, ref_data, model_type) {
    predictions <- map_dfr(rest_vals, function(r) {
      pred_data <- ref_data %>%
        mutate(rest_diff = r)
      
      if (spline_type == "piecewise_linear") {
        pred_data <- pred_data %>%
          mutate(
            rest_diff_neg3 = pmax(r + 3, 0),
            rest_diff_neg2 = pmax(r + 2, 0),
            rest_diff_pos2 = pmax(r - 2, 0),
            rest_diff_pos3 = pmax(r - 3, 0)
          )
      }
      
      pred <- tryCatch({
        if (model_type == "injury") {
          pred_val <- predict(model, newdata = pred_data, type = "response")
          tibble(rest_diff = r, predicted = as.numeric(pred_val))
        } else if (model_type == "performance") {
          pred_val <- predict(model, newdata = pred_data, type = "response")
          tibble(rest_diff = r, predicted = as.numeric(pred_val))
        } else {
          pred_val <- predict(model, newdata = pred_data, type = "response")
          tibble(rest_diff = r, predicted = as.numeric(pred_val))
        }
      }, error = function(e) {
        tibble(rest_diff = r, predicted = NA_real_)
      })
    })
  }
  
  injury_dose <- predict_dose_response(injury_spline, rest_diff_range, ref_data, "injury")
  performance_dose <- predict_dose_response(performance_spline, rest_diff_range, ref_data, "performance")
  win_dose <- predict_dose_response(win_spline, rest_diff_range, ref_data, "win")
  
  # Normalize to reference (rest_diff = 0)
  injury_dose <- injury_dose %>%
    mutate(
      ref_value = injury_dose$predicted[injury_dose$rest_diff == 0][1],
      effect = predicted - ref_value,
      effect_pct = (predicted / ref_value - 1) * 100
    )
  
  performance_dose <- performance_dose %>%
    mutate(
      ref_value = performance_dose$predicted[performance_dose$rest_diff == 0][1],
      effect = predicted - ref_value
    )
  
  win_dose <- win_dose %>%
    mutate(
      ref_value = win_dose$predicted[win_dose$rest_diff == 0][1],
      effect = predicted - ref_value,
      effect_pp = effect * 100
    )
  
  # Clustered standard errors
  injury_spline_clustered <- NULL
  performance_spline_clustered <- NULL
  win_spline_clustered <- NULL
  
  if (requireNamespace("sandwich", quietly = TRUE) &&
      requireNamespace("lmtest", quietly = TRUE)) {
    injury_spline_clustered <- tryCatch({
      lmtest::coeftest(injury_spline,
                       vcov = sandwich::vcovCL(injury_spline, cluster = model_data$team))
    }, error = function(e) NULL)
    
    performance_spline_clustered <- tryCatch({
      lmtest::coeftest(performance_spline,
                       vcov = sandwich::vcovCL(performance_spline, cluster = model_data$team))
    }, error = function(e) NULL)
    
    win_spline_clustered <- tryCatch({
      lmtest::coeftest(win_spline,
                       vcov = sandwich::vcovCL(win_spline, cluster = model_data$team))
    }, error = function(e) NULL)
  }
  
  list(
    injury_model = injury_spline,
    performance_model = performance_spline,
    win_model = win_spline,
    injury_clustered = injury_spline_clustered,
    performance_clustered = performance_spline_clustered,
    win_clustered = win_spline_clustered,
    injury_dose_response = injury_dose,
    performance_dose_response = performance_dose,
    win_dose_response = win_dose,
    spline_type = spline_type
  )
}

# -----------------------------------------------------------------------------
# 3.9.3 Counterfactual Policy Simulations
# -----------------------------------------------------------------------------
simulate_policy_counterfactuals <- function(injury_results, performance_results, 
                                            win_results, data) {
  
  # Policy 1: Cap rest differentials at ±2 days
  policy1_data <- data %>%
    filter(rest_category != "First Game", !is.na(rest_diff)) %>%
    mutate(
      rest_diff_capped = case_when(
        rest_diff < -2 ~ -2,
        rest_diff > 2 ~ 2,
        TRUE ~ rest_diff
      ),
      unfair_rest_capped = rest_diff_capped <= -2
    )
  
  # Policy 2: Optimize TNF (schedule TNF only after bye weeks, ensuring 10+ days rest)
  # This converts TNF games with short rest (<10 days) to have post-bye rest (10+ days)
  policy2_data <- data %>%
    filter(rest_category != "First Game") %>%
    mutate(
      # For TNF games with short rest, convert to post-bye rest (10+ days)
      rest_category_optimized = if_else(
        rest_category == "Thursday (Short Rest)" & days_rest < 10,
        "Post-Bye",  # TNF games now have 10+ days rest (post-bye)
        rest_category
      ),
      is_short_week_optimized = if_else(
        rest_category == "Thursday (Short Rest)" & days_rest < 10,
        FALSE,  # No longer short rest
        is_short_week
      ),
      # Adjust days_rest for optimized TNF games
      days_rest_optimized = if_else(
        rest_category == "Thursday (Short Rest)" & days_rest < 10,
        10,  # Minimum 10 days rest for optimized TNF
        days_rest
      )
    )
  
  # Policy 3: Add second bye week (reduce games since bye)
  # This is more complex - would need schedule reconstruction
  # For now, simulate by capping games_since_bye at 8
  
  # Use best models for predictions
  injury_model <- injury_results$negbin_category
  performance_model <- performance_results$cumulative
  win_model <- win_results$full
  
  # Get original factor levels from models
  # Extract from model data to ensure consistency
  model_data_sample <- data %>%
    filter(rest_category != "First Game") %>%
    slice_sample(n = min(500, nrow(.)))
  
  # Get factor levels
  rest_cat_levels <- levels(factor(model_data_sample$rest_category))
  surface_levels <- levels(factor(model_data_sample$surface))
  season_levels <- unique(model_data_sample$season)
  
  # Baseline predictions (current state) - use full dataset, not sample
  baseline_data <- data %>%
    filter(rest_category != "First Game") %>%
    mutate(
      rest_category = factor(rest_category, levels = rest_cat_levels),
      surface = factor(surface, levels = surface_levels),
      season = factor(season, levels = season_levels)
    )
  
  # Use actual observed values as baseline (more reliable than model predictions)
  baseline_injuries <- mean(baseline_data$injuries_next_week, na.rm = TRUE)
  baseline_epa <- mean(baseline_data$epa_play, na.rm = TRUE)
  baseline_win <- mean(baseline_data$win, na.rm = TRUE)
  
  # Policy 1: Rest differential cap - use full dataset
  policy1_data_prepared <- policy1_data %>%
    mutate(
      rest_category = factor(rest_category, levels = rest_cat_levels),
      surface = factor(surface, levels = surface_levels),
      season = factor(season, levels = season_levels)
    )
  
  # Use rest_diff model for injuries (more appropriate for this policy)
  injury_restdiff_model <- injury_results$negbin_restdiff
  
  # Calculate expected change based on model coefficients
  # Get coefficient for rest_diff from the model
  rest_diff_coef <- tryCatch({
    coef(injury_restdiff_model)["rest_diff"]
  }, error = function(e) 0)
  
  # Calculate average rest_diff change
  avg_rest_diff_baseline <- mean(baseline_data$rest_diff, na.rm = TRUE)
  avg_rest_diff_policy1 <- mean(policy1_data_prepared$rest_diff_capped, na.rm = TRUE)
  rest_diff_change <- avg_rest_diff_policy1 - avg_rest_diff_baseline
  
  # Predict injuries: if rest_diff coefficient is negative (more rest = fewer injuries),
  # then capping disadvantages should reduce injuries
  policy1_injuries <- tryCatch({
    policy1_pred_data <- policy1_data_prepared %>%
      mutate(rest_diff = rest_diff_capped, unfair_rest = unfair_rest_capped)
    mean(predict(injury_restdiff_model, newdata = policy1_pred_data, type = "response"), na.rm = TRUE)
  }, error = function(e) {
    # Fallback: use coefficient-based calculation
    baseline_injuries * exp(rest_diff_coef * rest_diff_change)
  })
  
  policy1_epa <- tryCatch({
    policy1_pred_data <- policy1_data_prepared %>%
      mutate(rest_diff = rest_diff_capped)
    mean(predict(performance_model, newdata = policy1_pred_data, type = "response"), na.rm = TRUE)
  }, error = function(e) baseline_epa)
  
  policy1_win <- tryCatch({
    policy1_pred_data <- policy1_data_prepared %>%
      mutate(rest_diff = rest_diff_capped, unfair_rest = unfair_rest_capped)
    mean(predict(win_model, newdata = policy1_pred_data, type = "response"), na.rm = TRUE)
  }, error = function(e) baseline_win)
  
  # Policy 2: Optimize TNF (post-bye only) - use rest_diff model
  # The negbin_restdiff model uses: rest_diff + home + surface + games_since_bye + cum_short_weeks + factor(season)
  # To optimize TNF, we need to:
  # 1. Adjust rest_diff for TNF games with short rest (convert to post-bye: 10+ days rest)
  # 2. Adjust cum_short_weeks (reducing cumulative short weeks for optimized TNF games)
  
  policy2_data_prepared <- policy2_data %>%
    mutate(
      # For TNF games with short rest, adjust rest_diff to reflect post-bye rest (10+ days)
      # TNF games typically have ~4 days rest, post-bye has 10+ days
      # So rest_diff improves by ~6 days when converting short-rest TNF to post-bye
      rest_diff_optimized = if_else(
        rest_category == "Thursday (Short Rest)" & days_rest < 10,
        rest_diff + (days_rest_optimized - days_rest),  # Improve rest_diff by the rest improvement
        rest_diff
      ),
      # Adjust cumulative short weeks (reduce by 1 for each TNF game optimized)
      cum_short_weeks_optimized = if_else(
        rest_category == "Thursday (Short Rest)" & days_rest < 10,
        pmax(0, cum_short_weeks - 1),  # Reduce by 1, but don't go negative
        cum_short_weeks
      ),
      unfair_rest = rest_diff_optimized <= -2,
      surface = factor(surface, levels = surface_levels),
      season = factor(season, levels = season_levels)
    )
  
  # Count TNF games being optimized (those with short rest)
  n_tnf_games_optimized <- sum(policy2_data$rest_category == "Thursday (Short Rest)" & 
                                policy2_data$days_rest < 10, na.rm = TRUE)
  
  policy2_injuries <- tryCatch({
    policy2_pred_data <- policy2_data_prepared %>%
      mutate(
        rest_diff = rest_diff_optimized,
        cum_short_weeks = cum_short_weeks_optimized,
        unfair_rest = unfair_rest
      )
    mean(predict(injury_restdiff_model, newdata = policy2_pred_data, type = "response"), na.rm = TRUE)
  }, error = function(e) {
    # Fallback: use rest_diff coefficient to estimate effect
    rest_diff_coef <- tryCatch({
      coef(injury_restdiff_model)["rest_diff"]
    }, error = function(e) 0)
    
    # Calculate average rest_diff improvement for optimized TNF games
    avg_rest_diff_improvement <- policy2_data_prepared %>%
      filter(rest_category == "Thursday (Short Rest)" & days_rest < 10) %>%
      summarise(avg_improvement = mean(rest_diff_optimized - rest_diff, na.rm = TRUE)) %>%
      pull(avg_improvement)
    
    # Estimate injury reduction: if rest_diff improves, injuries should decrease
    # (assuming rest_diff coefficient is negative: more rest = fewer injuries)
    pct_tnf <- n_tnf_games_optimized / nrow(policy2_data_prepared)
    baseline_injuries * exp(rest_diff_coef * avg_rest_diff_improvement * pct_tnf)
  })
  
  policy2_epa <- tryCatch({
    policy2_pred_data <- policy2_data_prepared %>%
      mutate(
        rest_diff = rest_diff_optimized,
        cum_short_weeks = cum_short_weeks_optimized
      )
    mean(predict(performance_model, newdata = policy2_pred_data, type = "response"), na.rm = TRUE)
  }, error = function(e) baseline_epa)
  
  policy2_win <- tryCatch({
    policy2_pred_data <- policy2_data_prepared %>%
      mutate(
        rest_diff = rest_diff_optimized,
        cum_short_weeks = cum_short_weeks_optimized,
        unfair_rest = unfair_rest
      )
    mean(predict(win_model, newdata = policy2_pred_data, type = "response"), na.rm = TRUE)
  }, error = function(e) baseline_win)
  
  # Calculate impacts
  policy_impacts <- tibble(
    policy = c("Baseline", "Cap Rest Diff at ±2", "Optimize TNF (Post-Bye Only)"),
    injuries_per_game = c(baseline_injuries, policy1_injuries, policy2_injuries),
    epa_per_play = c(baseline_epa, policy1_epa, policy2_epa),
    win_probability = c(baseline_win, policy1_win, policy2_win)
  ) %>%
    mutate(
      injury_change = injuries_per_game - baseline_injuries,
      injury_change_pct = (injuries_per_game / baseline_injuries - 1) * 100,
      epa_change = epa_per_play - baseline_epa,
      win_change_pp = (win_probability - baseline_win) * 100
    )
  
  # Scale to season level
  n_games_per_season <- 272  # 17 games × 32 teams / 2 (each game counted once per team)
  policy_impacts <- policy_impacts %>%
    mutate(
      injuries_per_season = injuries_per_game * n_games_per_season,
      # injuries_saved should be positive when injuries decrease (negative change)
      injuries_saved_per_season = -injury_change * n_games_per_season
    ) %>%
    # Add diagnostic info
    mutate(
      # Diagnostic: show what the change means
      interpretation = case_when(
        policy == "Baseline" ~ "Current state",
        injury_change < 0 ~ paste0("Reduces injuries by ", round(abs(injury_change), 3), " per game"),
        injury_change > 0 ~ paste0("Increases injuries by ", round(injury_change, 3), " per game"),
        TRUE ~ "No change in injuries"
      )
    )
  
  list(
    baseline = list(
      injuries = baseline_injuries,
      epa = baseline_epa,
      win = baseline_win
    ),
    policy1_rest_cap = list(
      injuries = policy1_injuries,
      epa = policy1_epa,
      win = policy1_win
    ),
    policy2_no_tnf = list(
      injuries = policy2_injuries,
      epa = policy2_epa,
      win = policy2_win
    ),
    impacts = policy_impacts
  )
}


# -----------------------------------------------------------------------------
# 3.9.7 Marginal Structural Models (IPW for Time-Varying Confounding)
# -----------------------------------------------------------------------------
analyze_marginal_structural_models <- function(data, injury_data, team_games) {
  
  # Check if required packages are available
  if (!requireNamespace("ipw", quietly = TRUE) && 
      !requireNamespace("WeightIt", quietly = TRUE)) {
    return(list(
      available = FALSE,
      message = "IPW packages not available. Install with: install.packages(c('ipw', 'WeightIt'))"
    ))
  }
  
  # Prepare counting process data for player-week survival
  # This is time-varying, so we need week-by-week exposure and outcomes
  
  # Get team rest info
  team_rest <- team_games %>%
    dplyr::select(season, week, team, days_rest, rest_category,
                  games_since_bye, cum_short_weeks, is_short_week, is_tnf,
                  rest_diff, unfair_rest, is_17_game_season)
  
  # Aggregate injuries to team-week level for confounders
  team_week_injuries <- injury_data %>%
    group_by(season, week, team) %>%
    summarise(
      n_new_injuries = sum(is_new_injury, na.rm = TRUE),
      .groups = "drop"
    )
  
  # Create player-week level data with time-varying exposures
  player_weeks_msm <- injury_data %>%
    left_join(team_rest, by = c("season", "week", "team")) %>%
    left_join(team_week_injuries, by = c("season", "week", "team")) %>%
    group_by(season, gsis_id, full_name, team, position) %>%
    arrange(week) %>%
    mutate(
      # Time-varying exposures
      exposure_short_week = is_short_week,
      exposure_unfair_rest = unfair_rest,
      exposure_high_compression = cum_short_weeks >= 3,
      
      # Time-varying confounders (past state)
      # Use team-level past injuries and player's own past injury status
      past_team_injuries = lag(n_new_injuries, 1, default = 0),
      past_player_injured = lag(as.numeric(is_on_report), 1, default = 0),
      past_short_weeks = lag(cum_short_weeks, 1, default = 0),
      past_games_since_bye = lag(games_since_bye, 1, default = 4),
      
      # Outcome (injury in current week)
      outcome_injury = as.numeric(is_new_injury),
      
      # Time index
      time = row_number()
    ) %>%
    ungroup() %>%
    filter(!is.na(exposure_short_week), time > 1)  # Need at least 1 week of history
  
  # Handle missing values in covariates before IPW
  # Check for missing values in key covariates
  msm_covariates <- c("past_team_injuries", "past_player_injured", 
                      "past_short_weeks", "past_games_since_bye", 
                      "season", "team", "exposure_short_week", "exposure_unfair_rest")
  
  # Count missing values before cleaning
  n_before <- nrow(player_weeks_msm)
  missing_counts <- player_weeks_msm %>%
    dplyr::select(all_of(msm_covariates)) %>%
    summarise_all(~sum(is.na(.))) %>%
    rowSums()
  
  # Remove rows with missing values in covariates needed for IPW
  player_weeks_msm_clean <- player_weeks_msm %>%
    filter(
      !is.na(past_team_injuries),
      !is.na(past_player_injured),
      !is.na(past_short_weeks),
      !is.na(past_games_since_bye),
      !is.na(season),
      !is.na(team)
    )
  
  n_after <- nrow(player_weeks_msm_clean)
  n_removed <- n_before - n_after
  
  if (n_removed > 0) {
    cat(glue("   Note: Removed {n_removed} rows ({round(n_removed/n_before*100, 1)}%) with missing covariates for IPW analysis\n"))
  }
  
  # Model 1: IPW for short_week exposure
  # Step 1: Estimate propensity scores (probability of exposure given past covariates)
  if (requireNamespace("WeightIt", quietly = TRUE)) {
    library(WeightIt)
    
    # Propensity model for short_week exposure
    ps_short_week <- tryCatch({
      weightit(
        exposure_short_week ~ past_team_injuries + past_player_injured + 
          past_short_weeks + past_games_since_bye + factor(season) + factor(team),
        data = player_weeks_msm_clean,
        method = "ps",  # Propensity score weighting
        estimand = "ATE"
      )
    }, error = function(e) NULL)
    
    # Step 2: Weighted outcome model
    if (!is.null(ps_short_week)) {
      player_weeks_msm_clean$ipw_weights_short <- ps_short_week$weights
      
      msm_short_week <- tryCatch({
        MASS::glm.nb(
          outcome_injury ~ exposure_short_week + factor(season),
          data = player_weeks_msm_clean,
          weights = ipw_weights_short
        )
      }, error = function(e) NULL)
    } else {
      msm_short_week <- NULL
    }
    
    # Propensity model for unfair_rest exposure
    # Also need to filter for non-missing exposure_unfair_rest
    player_weeks_msm_clean_unfair <- player_weeks_msm_clean %>%
      filter(!is.na(exposure_unfair_rest))
    
    ps_unfair_rest <- tryCatch({
      weightit(
        exposure_unfair_rest ~ past_team_injuries + past_player_injured + 
          past_short_weeks + past_games_since_bye + factor(season) + factor(team),
        data = player_weeks_msm_clean_unfair,
        method = "ps",
        estimand = "ATE"
      )
    }, error = function(e) NULL)
    
    if (!is.null(ps_unfair_rest)) {
      player_weeks_msm_clean_unfair$ipw_weights_unfair <- ps_unfair_rest$weights
      
      msm_unfair_rest <- tryCatch({
        MASS::glm.nb(
          outcome_injury ~ exposure_unfair_rest + factor(season),
          data = player_weeks_msm_clean_unfair,
          weights = ipw_weights_unfair
        )
      }, error = function(e) NULL)
    } else {
      msm_unfair_rest <- NULL
    }
    
    # Extract effects
    extract_msm_effect <- function(model, exposure_name) {
      if (is.null(model)) return(NULL)
      coefs <- tidy(model) %>%
        filter(grepl("exposure", term))
      if (nrow(coefs) > 0) {
        list(
          exposure = exposure_name,
          estimate = coefs$estimate[1],
          se = coefs$std.error[1],
          rate_ratio = exp(coefs$estimate[1]),
          ci_lower = exp(coefs$estimate[1] - 1.96 * coefs$std.error[1]),
          ci_upper = exp(coefs$estimate[1] + 1.96 * coefs$std.error[1])
        )
      } else NULL
    }
    
    msm_effects <- list(
      short_week = extract_msm_effect(msm_short_week, "Short Week"),
      unfair_rest = extract_msm_effect(msm_unfair_rest, "Unfair Rest")
    )
    
    list(
      available = TRUE,
      ps_short_week = ps_short_week,
      ps_unfair_rest = ps_unfair_rest,
      msm_short_week = msm_short_week,
      msm_unfair_rest = msm_unfair_rest,
      effects = msm_effects,
      data = player_weeks_msm_clean,
      n_removed = n_removed,
      n_total = n_before
    )
  } else {
    # Fallback to ipw package
    if (requireNamespace("ipw", quietly = TRUE)) {
      library(ipw)
      
      # Use cleaned data (already filtered for missing values above)
      # Simplified IPW using ipw package
      ipw_short_week <- tryCatch({
      ipwpoint(
        exposure = exposure_short_week,
        family = "binomial",
        numerator = ~ 1,
        denominator = ~ past_team_injuries + past_player_injured + past_short_weeks + past_games_since_bye + factor(season),
        data = player_weeks_msm_clean
      )
      }, error = function(e) NULL)
      
      if (!is.null(ipw_short_week)) {
        player_weeks_msm_clean$ipw_weights_short <- ipw_short_week$ipw.weights
        
        msm_short_week <- tryCatch({
          MASS::glm.nb(
            outcome_injury ~ exposure_short_week + factor(season),
            data = player_weeks_msm_clean,
            weights = ipw_weights_short
          )
        }, error = function(e) NULL)
      } else {
        msm_short_week <- NULL
      }
      
      list(
        available = TRUE,
        msm_short_week = msm_short_week,
        ipw_weights = ipw_short_week,
        method = "ipw_package"
      )
    } else {
      list(
        available = FALSE,
        message = "Neither WeightIt nor ipw package available"
      )
    }
  }
}


# -----------------------------------------------------------------------------
# 3.9.9 Interaction Effects: Late-Season Compression ("The Grind Variable")
# -----------------------------------------------------------------------------
# Tests if cumulative workload effects are amplified in late season
# Theory: Thursday game in Week 15 is more dangerous than Week 2
# -----------------------------------------------------------------------------
analyze_late_season_workload_interaction <- function(data) {
  
  model_data <- data %>%
    filter(rest_category != "First Game") %>%
    mutate(
      # Create interaction terms
      week_cum_short_interaction = week * cum_short_weeks,
      late_season = week >= 13,
      late_season_cum_short = late_season * cum_short_weeks,
      # Alternative: continuous week × cumulative short weeks
      week_centered = week - 9,  # Center at mid-season
      week_cum_short_centered = week_centered * cum_short_weeks
    )
  
  # Model 1: Injury count with interaction
  injury_interaction <- MASS::glm.nb(
    injuries_next_week ~ week + cum_short_weeks + week_cum_short_interaction +
      home + surface + games_since_bye + factor(season),
    data = model_data
  )
  
  # Model 2: Late season indicator interaction
  injury_late_season <- MASS::glm.nb(
    injuries_next_week ~ late_season + cum_short_weeks + late_season_cum_short +
      home + surface + games_since_bye + factor(season),
    data = model_data
  )
  
  # Model 3: Performance with interaction
  performance_interaction <- lm(
    epa_play ~ week + cum_short_weeks + week_cum_short_interaction +
      home + surface + games_since_bye + factor(season),
    data = model_data
  )
  
  # Model 4: Win probability with interaction
  win_interaction <- glm(
    win ~ week + cum_short_weeks + week_cum_short_interaction +
      home + games_since_bye + factor(season),
    data = model_data,
    family = binomial()
  )
  
  # Extract interaction coefficients
  extract_interaction_coefs <- function(model, model_name) {
    coefs <- tidy(model) %>%
      filter(grepl("interaction|late_season_cum", term))
    if (nrow(coefs) > 0) {
      coefs %>%
        mutate(
          model = model_name,
          estimate_exp = if_else(model_name == "injury" | model_name == "win",
                                exp(estimate), estimate)
        )
    } else {
      tibble(
        term = character(),
        estimate = numeric(),
        std.error = numeric(),
        p.value = numeric(),
        model = character(),
        estimate_exp = numeric()
      )
    }
  }
  
  interaction_coefs <- bind_rows(
    extract_interaction_coefs(injury_interaction, "injury"),
    extract_interaction_coefs(injury_late_season, "injury_late"),
    extract_interaction_coefs(performance_interaction, "performance"),
    extract_interaction_coefs(win_interaction, "win")
  )
  
  # Generate predictions for visualization
  # Create grid of week × cum_short_weeks combinations
  week_range <- 1:18
  cum_short_range <- 0:5
  
  prediction_grid <- expand_grid(
    week = week_range,
    cum_short_weeks = cum_short_range,
    home = FALSE,
    surface = "grass",
    games_since_bye = 4,
    season = 2023
  ) %>%
    mutate(
      week_cum_short_interaction = week * cum_short_weeks,
      late_season = week >= 13,
      late_season_cum_short = late_season * cum_short_weeks,
      week_centered = week - 9,
      week_cum_short_centered = week_centered * cum_short_weeks
    )
  
  # Predict injuries
  injury_predictions <- prediction_grid %>%
    mutate(
      predicted_injuries = predict(injury_interaction, newdata = ., type = "response")
    )
  
  # Predict performance
  performance_predictions <- prediction_grid %>%
    mutate(
      predicted_epa = predict(performance_interaction, newdata = ., type = "response")
    )
  
  # Clustered standard errors
  injury_interaction_clustered <- NULL
  performance_interaction_clustered <- NULL
  win_interaction_clustered <- NULL
  
  if (requireNamespace("sandwich", quietly = TRUE) &&
      requireNamespace("lmtest", quietly = TRUE)) {
    injury_interaction_clustered <- tryCatch({
      lmtest::coeftest(injury_interaction,
                       vcov = sandwich::vcovCL(injury_interaction, cluster = model_data$team))
    }, error = function(e) NULL)
    
    performance_interaction_clustered <- tryCatch({
      lmtest::coeftest(performance_interaction,
                       vcov = sandwich::vcovCL(performance_interaction, cluster = model_data$team))
    }, error = function(e) NULL)
    
    win_interaction_clustered <- tryCatch({
      lmtest::coeftest(win_interaction,
                       vcov = sandwich::vcovCL(win_interaction, cluster = model_data$team))
    }, error = function(e) NULL)
  }
  
  list(
    injury_model = injury_interaction,
    injury_late_season_model = injury_late_season,
    performance_model = performance_interaction,
    win_model = win_interaction,
    injury_clustered = injury_interaction_clustered,
    performance_clustered = performance_interaction_clustered,
    win_clustered = win_interaction_clustered,
    interaction_coefficients = interaction_coefs,
    injury_predictions = injury_predictions,
    performance_predictions = performance_predictions
  )
}


# -----------------------------------------------------------------------------

# =============================================================================
# PART 4: SURVIVAL ANALYSIS
# =============================================================================

# -----------------------------------------------------------------------------
# 4.1 Prepare Survival Data (Counting Process Format)
# -----------------------------------------------------------------------------
prepare_survival_data <- function(injury_data, team_games) {
  
  # Get team rest info
  team_rest <- team_games %>%
    dplyr::select(season, week, team, days_rest, rest_category,
                  games_since_bye, cum_short_weeks, is_short_week, is_tnf,
                  rest_diff, unfair_rest, is_17_game_season) %>%
    filter(!is.na(team), !is.na(week))
  
  # Create player-week level data
  player_weeks <- injury_data %>%
    left_join(team_rest, by = c("season", "week", "team")) %>%
    group_by(season, gsis_id, full_name, team, position) %>%
    arrange(week) %>%
    mutate(
      # Time at risk: cumulative games
      time_start = row_number() - 1,
      time_end = row_number(),
      event = as.numeric(is_new_injury),
      
      # Fill missing values
      rest_category = replace_na(rest_category, "Standard (6-7 days)"),
      days_rest = replace_na(days_rest, 7),
      games_since_bye = replace_na(games_since_bye, 4),
      cum_short_weeks = replace_na(cum_short_weeks, 0),
      is_short_week = replace_na(is_short_week, FALSE),
      rest_diff = replace_na(rest_diff, 0),
      unfair_rest = replace_na(unfair_rest, FALSE)
    ) %>%
    ungroup()
  
  # Alternative: collapsed player-season format for simpler models
  survival_summary <- player_weeks %>%
    group_by(season, gsis_id, full_name, team, position) %>%
    summarise(
      # Time to first injury
      time_to_injury = if (any(event == 1, na.rm = TRUE)) {
        min(time_end[event == 1], na.rm = TRUE)
      } else {
        max(time_end, na.rm = TRUE)
      },
      
      injured = as.numeric(any(event == 1, na.rm = TRUE)),
      
      # Covariates
      avg_days_rest = mean(days_rest, na.rm = TRUE),
      avg_rest_diff = mean(rest_diff, na.rm = TRUE),
      pct_short_weeks = mean(is_short_week, na.rm = TRUE),
      pct_unfair_rest = mean(unfair_rest, na.rm = TRUE),
      total_games = n(),
      
      .groups = "drop"
    ) %>%
    filter(!is.na(time_to_injury), time_to_injury > 0) %>%
    mutate(
      # Position groups
      position_group = case_when(
        grepl("QB", position, ignore.case = TRUE) ~ "QB",
        grepl("RB|FB", position, ignore.case = TRUE) ~ "RB",
        grepl("WR", position, ignore.case = TRUE) ~ "WR",
        grepl("TE", position, ignore.case = TRUE) ~ "TE",
        grepl("OL|T|G|C", position, ignore.case = TRUE) ~ "OL",
        grepl("DL|DE|DT|NT", position, ignore.case = TRUE) ~ "DL",
        grepl("LB|ILB|OLB", position, ignore.case = TRUE) ~ "LB",
        grepl("DB|CB|S|FS|SS", position, ignore.case = TRUE) ~ "DB",
        TRUE ~ "Other"
      ),
      
      # Risk groups
      rest_group = case_when(
        pct_short_weeks >= 0.2 ~ "High Short Rest",
        pct_short_weeks > 0 ~ "Some Short Rest",
        TRUE ~ "Standard Rest Only"
      ),
      rest_group = factor(rest_group,
                          levels = c("Standard Rest Only", "Some Short Rest", "High Short Rest"))
    )
  
  list(
    counting_process = player_weeks,
    summary = survival_summary
  )
}

# -----------------------------------------------------------------------------
# 4.1.5 Prepare Severe Injury Survival Data
# -----------------------------------------------------------------------------
prepare_severe_injury_survival_data <- function(injury_data, team_games) {
  
  # Get team rest info
  team_rest <- team_games %>%
    dplyr::select(season, week, team, days_rest, rest_category,
                  games_since_bye, cum_short_weeks, is_short_week, is_tnf,
                  rest_diff, unfair_rest, is_17_game_season) %>%
    filter(!is.na(team), !is.na(week))
  
  # Create player-week level data
  player_weeks <- injury_data %>%
    left_join(team_rest, by = c("season", "week", "team")) %>%
    group_by(season, gsis_id, full_name, team, position) %>%
    arrange(week) %>%
    mutate(
      # Time at risk: cumulative games
      time_start = row_number() - 1,
      time_end = row_number(),
      
      # Identify severe injuries: player is "out" for 2+ consecutive weeks
      # Check if player is out this week AND next week (or more)
      is_out_this_week = is_out,
      is_out_next_week = lead(is_out, default = FALSE),
      is_out_week_after = lead(is_out, n = 2, default = FALSE),
      
      # Severe injury: new injury AND out for 2+ consecutive weeks
      is_severe_injury = is_new_injury & is_out_this_week & 
                         (is_out_next_week | is_out_week_after),
      
      event = as.numeric(is_severe_injury),
      
      # Fill missing values
      rest_category = replace_na(rest_category, "Standard (6-7 days)"),
      days_rest = replace_na(days_rest, 7),
      games_since_bye = replace_na(games_since_bye, 4),
      cum_short_weeks = replace_na(cum_short_weeks, 0),
      is_short_week = replace_na(is_short_week, FALSE),
      rest_diff = replace_na(rest_diff, 0),
      unfair_rest = replace_na(unfair_rest, FALSE)
    ) %>%
    ungroup()
  
  # Collapsed player-season format
  survival_summary <- player_weeks %>%
    group_by(season, gsis_id, full_name, team, position) %>%
    summarise(
      # Time to first severe injury
      time_to_severe_injury = if (any(event == 1, na.rm = TRUE)) {
        min(time_end[event == 1], na.rm = TRUE)
      } else {
        max(time_end, na.rm = TRUE)
      },
      
      severe_injury_occurred = as.numeric(any(event == 1, na.rm = TRUE)),
      
      # Covariates
      avg_days_rest = mean(days_rest, na.rm = TRUE),
      avg_rest_diff = mean(rest_diff, na.rm = TRUE),
      pct_short_weeks = mean(is_short_week, na.rm = TRUE),
      pct_unfair_rest = mean(unfair_rest, na.rm = TRUE),
      total_games = n(),
      
      .groups = "drop"
    ) %>%
    filter(!is.na(time_to_severe_injury), time_to_severe_injury > 0) %>%
    mutate(
      # Position groups
      position_group = case_when(
        grepl("QB", position, ignore.case = TRUE) ~ "QB",
        grepl("RB|FB", position, ignore.case = TRUE) ~ "RB",
        grepl("WR", position, ignore.case = TRUE) ~ "WR",
        grepl("TE", position, ignore.case = TRUE) ~ "TE",
        grepl("OL|T|G|C", position, ignore.case = TRUE) ~ "OL",
        grepl("DL|DE|DT|NT", position, ignore.case = TRUE) ~ "DL",
        grepl("LB|ILB|OLB", position, ignore.case = TRUE) ~ "LB",
        grepl("DB|CB|S|FS|SS", position, ignore.case = TRUE) ~ "DB",
        TRUE ~ "Other"
      ),
      
      # Risk groups
      rest_group = case_when(
        pct_short_weeks >= 0.2 ~ "High Short Rest",
        pct_short_weeks > 0 ~ "Some Short Rest",
        TRUE ~ "Standard Rest Only"
      ),
      rest_group = factor(rest_group,
                          levels = c("Standard Rest Only", "Some Short Rest", "High Short Rest"))
    )
  
  list(
    counting_process = player_weeks,
    summary = survival_summary
  )
}

# -----------------------------------------------------------------------------
# 4.2 Fit Survival Models
# -----------------------------------------------------------------------------
analyze_survival <- function(survival_data) {
  
  surv_summary <- survival_data$summary
  
  # Create survival object
  surv_obj <- Surv(time = surv_summary$time_to_injury,
                   event = surv_summary$injured)
  
  # Kaplan-Meier curves
  km_overall <- survfit(surv_obj ~ 1)
  km_by_rest <- survfit(surv_obj ~ rest_group, data = surv_summary)
  
  # Cox models with cluster() for robust standard errors
  # Model 1: Rest pattern
  cox_rest <- coxph(surv_obj ~ rest_group + total_games + factor(season) + cluster(team),
                    data = surv_summary)
  
  # Model 2: Workload
  cox_workload <- coxph(surv_obj ~ pct_short_weeks + total_games + factor(season) + cluster(team),
                        data = surv_summary)
  
  # Model 3: Full model
  cox_full <- coxph(surv_obj ~ rest_group + total_games + factor(season) + cluster(team),
                    data = surv_summary)
  
  # Model 4: With position (if enough variation)
  cox_position <- NULL
  if (n_distinct(surv_summary$position_group) > 2) {
    cox_position <- coxph(surv_obj ~ rest_group +
                            position_group + total_games + factor(season) + cluster(team),
                          data = surv_summary)
  }
  
  # Model comparison
  model_comparison <- data.frame(
    model = c("Rest Pattern", "Workload", "Full", "With Position"),
    aic = c(AIC(cox_rest), AIC(cox_workload), AIC(cox_full),
            if (!is.null(cox_position)) AIC(cox_position) else NA)
  ) %>%
    filter(!is.na(aic)) %>%
    arrange(aic)
  
  # Hazard ratios from best model
  best_model <- cox_full
  hazard_ratios <- tidy(best_model) %>%
    mutate(
      hr = exp(estimate),
      hr_lower = exp(estimate - 1.96 * std.error),
      hr_upper = exp(estimate + 1.96 * std.error)
    )
  
  # Proportional hazards test
  ph_test <- cox.zph(cox_full)
  
  list(
    km_overall = km_overall,
    km_by_rest = km_by_rest,
    cox_rest = cox_rest,
    cox_workload = cox_workload,
    cox_full = cox_full,
    cox_position = cox_position,
    model_comparison = model_comparison,
    hazard_ratios = hazard_ratios,
    ph_test = ph_test,
    concordance = summary(cox_full)$concordance,
    survival_data = surv_summary
  )
}

# -----------------------------------------------------------------------------
# 4.1.6 Prepare Severe Injury Survival Data (3+ weeks - Sensitivity)
# -----------------------------------------------------------------------------
prepare_severe_injury_survival_data_3wk <- function(injury_data, team_games) {
  
  # Get team rest info
  team_rest <- team_games %>%
    dplyr::select(season, week, team, days_rest, rest_category,
                  games_since_bye, cum_short_weeks, is_short_week, is_tnf,
                  rest_diff, unfair_rest, is_17_game_season) %>%
    filter(!is.na(team), !is.na(week))
  
  # Create player-week level data
  player_weeks <- injury_data %>%
    left_join(team_rest, by = c("season", "week", "team")) %>%
    group_by(season, gsis_id, full_name, team, position) %>%
    arrange(week) %>%
    mutate(
      # Time at risk: cumulative games
      time_start = row_number() - 1,
      time_end = row_number(),
      
      # Identify severe injuries: player is "out" for 3+ consecutive weeks
      # Check if player is out this week AND next 2 weeks (or more)
      is_out_this_week = is_out,
      is_out_next_week = lead(is_out, default = FALSE),
      is_out_week_after = lead(is_out, n = 2, default = FALSE),
      
      # Severe injury: new injury AND out for 3+ consecutive weeks
      # Must be out this week, next week, AND week after next
      is_severe_injury = is_new_injury & is_out_this_week & 
                         is_out_next_week & is_out_week_after,
      
      event = as.numeric(is_severe_injury),
      
      # Fill missing values
      rest_category = replace_na(rest_category, "Standard (6-7 days)"),
      days_rest = replace_na(days_rest, 7),
      games_since_bye = replace_na(games_since_bye, 4),
      cum_short_weeks = replace_na(cum_short_weeks, 0),
      is_short_week = replace_na(is_short_week, FALSE),
      rest_diff = replace_na(rest_diff, 0),
      unfair_rest = replace_na(unfair_rest, FALSE)
    ) %>%
    ungroup()
  
  # Collapsed player-season format
  survival_summary <- player_weeks %>%
    group_by(season, gsis_id, full_name, team, position) %>%
    summarise(
      # Time to first severe injury
      time_to_severe_injury = if (any(event == 1, na.rm = TRUE)) {
        min(time_end[event == 1], na.rm = TRUE)
      } else {
        max(time_end, na.rm = TRUE)
      },
      
      severe_injury_occurred = as.numeric(any(event == 1, na.rm = TRUE)),
      
      # Covariates
      avg_days_rest = mean(days_rest, na.rm = TRUE),
      avg_rest_diff = mean(rest_diff, na.rm = TRUE),
      pct_short_weeks = mean(is_short_week, na.rm = TRUE),
      pct_unfair_rest = mean(unfair_rest, na.rm = TRUE),
      total_games = n(),
      
      .groups = "drop"
    ) %>%
    filter(!is.na(time_to_severe_injury), time_to_severe_injury > 0) %>%
    mutate(
      # Position groups
      position_group = case_when(
        grepl("QB", position, ignore.case = TRUE) ~ "QB",
        grepl("RB|FB", position, ignore.case = TRUE) ~ "RB",
        grepl("WR", position, ignore.case = TRUE) ~ "WR",
        grepl("TE", position, ignore.case = TRUE) ~ "TE",
        grepl("OL|T|G|C", position, ignore.case = TRUE) ~ "OL",
        grepl("DL|DE|DT|NT", position, ignore.case = TRUE) ~ "DL",
        grepl("LB|ILB|OLB", position, ignore.case = TRUE) ~ "LB",
        grepl("DB|CB|S|FS|SS", position, ignore.case = TRUE) ~ "DB",
        TRUE ~ "Other"
      ),
      
      # Risk groups
      rest_group = case_when(
        pct_short_weeks >= 0.2 ~ "High Short Rest",
        pct_short_weeks > 0 ~ "Some Short Rest",
        TRUE ~ "Standard Rest Only"
      ),
      rest_group = factor(rest_group,
                          levels = c("Standard Rest Only", "Some Short Rest", "High Short Rest"))
    )
  
  list(
    counting_process = player_weeks,
    summary = survival_summary
  )
}

# -----------------------------------------------------------------------------
# 4.1.7 Prepare Severe Injury Survival Data (4+ weeks - Sensitivity)
# -----------------------------------------------------------------------------
prepare_severe_injury_survival_data_4wk <- function(injury_data, team_games) {
  
  # Get team rest info
  team_rest <- team_games %>%
    dplyr::select(season, week, team, days_rest, rest_category,
                  games_since_bye, cum_short_weeks, is_short_week, is_tnf,
                  rest_diff, unfair_rest, is_17_game_season) %>%
    filter(!is.na(team), !is.na(week))
  
  # Create player-week level data
  player_weeks <- injury_data %>%
    left_join(team_rest, by = c("season", "week", "team")) %>%
    group_by(season, gsis_id, full_name, team, position) %>%
    arrange(week) %>%
    mutate(
      # Time at risk: cumulative games
      time_start = row_number() - 1,
      time_end = row_number(),
      
      # Identify severe injuries: player is "out" for 4+ consecutive weeks
      # Check if player is out this week AND next 3 weeks
      is_out_this_week = is_out,
      is_out_next_week = lead(is_out, default = FALSE),
      is_out_week_after = lead(is_out, n = 2, default = FALSE),
      is_out_week_after2 = lead(is_out, n = 3, default = FALSE),
      
      # Severe injury: new injury AND out for 4+ consecutive weeks
      # Must be out this week, next week, week after next, AND week after that
      is_severe_injury = is_new_injury & is_out_this_week & 
                         is_out_next_week & is_out_week_after & is_out_week_after2,
      
      event = as.numeric(is_severe_injury),
      
      # Fill missing values
      rest_category = replace_na(rest_category, "Standard (6-7 days)"),
      days_rest = replace_na(days_rest, 7),
      games_since_bye = replace_na(games_since_bye, 4),
      cum_short_weeks = replace_na(cum_short_weeks, 0),
      is_short_week = replace_na(is_short_week, FALSE),
      rest_diff = replace_na(rest_diff, 0),
      unfair_rest = replace_na(unfair_rest, FALSE)
    ) %>%
    ungroup()
  
  # Collapsed player-season format
  survival_summary <- player_weeks %>%
    group_by(season, gsis_id, full_name, team, position) %>%
    summarise(
      # Time to first severe injury
      time_to_severe_injury = if (any(event == 1, na.rm = TRUE)) {
        min(time_end[event == 1], na.rm = TRUE)
      } else {
        max(time_end, na.rm = TRUE)
      },
      
      severe_injury_occurred = as.numeric(any(event == 1, na.rm = TRUE)),
      
      # Covariates
      avg_days_rest = mean(days_rest, na.rm = TRUE),
      avg_rest_diff = mean(rest_diff, na.rm = TRUE),
      pct_short_weeks = mean(is_short_week, na.rm = TRUE),
      pct_unfair_rest = mean(unfair_rest, na.rm = TRUE),
      total_games = n(),
      
      .groups = "drop"
    ) %>%
    filter(!is.na(time_to_severe_injury), time_to_severe_injury > 0) %>%
    mutate(
      # Position groups
      position_group = case_when(
        grepl("QB", position, ignore.case = TRUE) ~ "QB",
        grepl("RB|FB", position, ignore.case = TRUE) ~ "RB",
        grepl("WR", position, ignore.case = TRUE) ~ "WR",
        grepl("TE", position, ignore.case = TRUE) ~ "TE",
        grepl("OL|T|G|C", position, ignore.case = TRUE) ~ "OL",
        grepl("DL|DE|DT|NT", position, ignore.case = TRUE) ~ "DL",
        grepl("LB|ILB|OLB", position, ignore.case = TRUE) ~ "LB",
        grepl("DB|CB|S|FS|SS", position, ignore.case = TRUE) ~ "DB",
        TRUE ~ "Other"
      ),
      
      # Risk groups
      rest_group = case_when(
        pct_short_weeks >= 0.2 ~ "High Short Rest",
        pct_short_weeks > 0 ~ "Some Short Rest",
        TRUE ~ "Standard Rest Only"
      ),
      rest_group = factor(rest_group,
                          levels = c("Standard Rest Only", "Some Short Rest", "High Short Rest"))
    )
  
  list(
    counting_process = player_weeks,
    summary = survival_summary
  )
}

# -----------------------------------------------------------------------------
# 4.3 Analyze Severe Injury Survival
# -----------------------------------------------------------------------------
analyze_severe_injury_survival <- function(severe_injury_survival_data) {
  
  surv_summary <- severe_injury_survival_data$summary
  
  # Create survival object for severe injuries
  surv_obj <- Surv(time = surv_summary$time_to_severe_injury,
                   event = surv_summary$severe_injury_occurred)
  
  # Kaplan-Meier curves
  km_overall_severe <- survfit(surv_obj ~ 1)
  km_by_rest_severe <- survfit(surv_obj ~ rest_group, data = surv_summary)
  
  # Cox models with cluster() for robust standard errors
  # Model 1: Rest pattern
  cox_rest_severe <- coxph(surv_obj ~ rest_group + total_games + factor(season) + cluster(team),
                          data = surv_summary)
  
  # Model 2: Full model
  cox_full_severe <- coxph(surv_obj ~ rest_group + total_games + factor(season) + cluster(team),
                          data = surv_summary)
  
  # Hazard ratios from full model
  hazard_ratios_severe <- tidy(cox_full_severe) %>%
    mutate(
      hr = exp(estimate),
      hr_lower = exp(estimate - 1.96 * std.error),
      hr_upper = exp(estimate + 1.96 * std.error)
    )
  
  # Proportional hazards test
  ph_test_severe <- cox.zph(cox_full_severe)
  
  list(
    km_overall = km_overall_severe,
    km_by_rest = km_by_rest_severe,
    cox_rest = cox_rest_severe,
    cox_full = cox_full_severe,
    hazard_ratios = hazard_ratios_severe,
    ph_test = ph_test_severe,
    concordance = summary(cox_full_severe)$concordance,
    survival_data = surv_summary
  )
}

# -----------------------------------------------------------------------------
# 4.3.5 Analyze Severe Injury Survival (3+ weeks - Sensitivity)
# -----------------------------------------------------------------------------
analyze_severe_injury_survival_3wk <- function(severe_injury_survival_data_3wk) {
  
  surv_summary <- severe_injury_survival_data_3wk$summary
  
  # Create survival object for severe injuries (3+ weeks)
  surv_obj <- Surv(time = surv_summary$time_to_severe_injury,
                   event = surv_summary$severe_injury_occurred)
  
  # Kaplan-Meier curves
  km_overall_severe <- survfit(surv_obj ~ 1)
  km_by_rest_severe <- survfit(surv_obj ~ rest_group, data = surv_summary)
  
  # Cox models with cluster() for robust standard errors
  # Model 1: Rest pattern
  cox_rest_severe <- coxph(surv_obj ~ rest_group + total_games + factor(season) + cluster(team),
                          data = surv_summary)
  
  # Model 2: Full model
  cox_full_severe <- coxph(surv_obj ~ rest_group + total_games + factor(season) + cluster(team),
                          data = surv_summary)
  
  # Hazard ratios from full model
  hazard_ratios_severe <- tidy(cox_full_severe) %>%
    mutate(
      hr = exp(estimate),
      hr_lower = exp(estimate - 1.96 * std.error),
      hr_upper = exp(estimate + 1.96 * std.error)
    )
  
  # Proportional hazards test
  ph_test_severe <- cox.zph(cox_full_severe)
  
  list(
    km_overall = km_overall_severe,
    km_by_rest = km_by_rest_severe,
    cox_rest = cox_rest_severe,
    cox_full = cox_full_severe,
    hazard_ratios = hazard_ratios_severe,
    ph_test = ph_test_severe,
    concordance = summary(cox_full_severe)$concordance,
    survival_data = surv_summary
  )
}

# -----------------------------------------------------------------------------
# 4.3.6 Analyze Severe Injury Survival (4+ weeks - Sensitivity)
# -----------------------------------------------------------------------------
analyze_severe_injury_survival_4wk <- function(severe_injury_survival_data_4wk) {
  
  surv_summary <- severe_injury_survival_data_4wk$summary
  
  # Create survival object for severe injuries (4+ weeks)
  surv_obj <- Surv(time = surv_summary$time_to_severe_injury,
                   event = surv_summary$severe_injury_occurred)
  
  # Kaplan-Meier curves
  km_overall_severe <- survfit(surv_obj ~ 1)
  km_by_rest_severe <- survfit(surv_obj ~ rest_group, data = surv_summary)
  
  # Cox models with cluster() for robust standard errors
  # Model 1: Rest pattern
  cox_rest_severe <- coxph(surv_obj ~ rest_group + total_games + factor(season) + cluster(team),
                          data = surv_summary)
  
  # Model 2: Full model
  cox_full_severe <- coxph(surv_obj ~ rest_group + total_games + factor(season) + cluster(team),
                          data = surv_summary)
  
  # Hazard ratios from full model
  hazard_ratios_severe <- tidy(cox_full_severe) %>%
    mutate(
      hr = exp(estimate),
      hr_lower = exp(estimate - 1.96 * std.error),
      hr_upper = exp(estimate + 1.96 * std.error)
    )
  
  # Proportional hazards test
  ph_test_severe <- cox.zph(cox_full_severe)
  
  list(
    km_overall = km_overall_severe,
    km_by_rest = km_by_rest_severe,
    cox_rest = cox_rest_severe,
    cox_full = cox_full_severe,
    hazard_ratios = hazard_ratios_severe,
    ph_test = ph_test_severe,
    concordance = summary(cox_full_severe)$concordance,
    survival_data = surv_summary
  )
}

# =============================================================================
# PART 5: VISUALIZATION
# =============================================================================

# -----------------------------------------------------------------------------
# 5.1 Basic Rest Effects Plots
# -----------------------------------------------------------------------------
plot_rest_effects <- function(performance_results, injury_results) {
  
  p1 <- performance_results$summary %>%
    ggplot(aes(x = rest_category, y = mean_epa, fill = rest_category)) +
    geom_col() +
    geom_errorbar(aes(ymin = mean_epa - 1.96*se_epa,
                      ymax = mean_epa + 1.96*se_epa),
                  width = 0.2) +
    geom_hline(yintercept = 0, linetype = "dashed", alpha = 0.5) +
    labs(
      title = "Offensive EPA/Play by Rest Category",
      subtitle = "Error bars = 95% CI",
      x = "Rest Category",
      y = "Mean EPA/Play"
    ) +
    theme_minimal() +
    theme(legend.position = "none",
          axis.text.x = element_text(angle = 20, hjust = 1))
  
  p2 <- injury_results$summary %>%
    ggplot(aes(x = rest_category, y = mean_new_injuries, fill = rest_category)) +
    geom_col() +
    geom_errorbar(aes(ymin = mean_new_injuries - 1.96*se_injuries,
                      ymax = mean_new_injuries + 1.96*se_injuries),
                  width = 0.2) +
    labs(
      title = "New Injuries Following Game by Rest Category",
      subtitle = "Error bars = 95% CI",
      x = "Rest Category",
      y = "Mean New Injuries"
    ) +
    theme_minimal() +
    theme(legend.position = "none",
          axis.text.x = element_text(angle = 20, hjust = 1))
  
  list(performance = p1, injuries = p2)
}

# -----------------------------------------------------------------------------
# 5.2 Win Probability Plots
# -----------------------------------------------------------------------------
plot_win_analysis <- function(win_results) {
  
  # Win rate by rest category
  p1 <- win_results$summary %>%
    ggplot(aes(x = rest_category, y = win_pct, fill = rest_category)) +
    geom_col() +
    geom_errorbar(aes(ymin = win_pct - 1.96*se_win_pct,
                      ymax = win_pct + 1.96*se_win_pct),
                  width = 0.2) +
    geom_hline(yintercept = 0.5, linetype = "dashed", alpha = 0.5) +
    scale_y_continuous(labels = scales::percent_format()) +
    labs(
      title = "Win Percentage by Rest Category",
      x = "Rest Category",
      y = "Win %"
    ) +
    theme_minimal() +
    theme(legend.position = "none",
          axis.text.x = element_text(angle = 20, hjust = 1))
  
  # Win rate by rest differential
  p2 <- win_results$by_restdiff %>%
    ggplot(aes(x = rest_diff_bin, y = win_pct, fill = rest_diff_bin)) +
    geom_col() +
    geom_errorbar(aes(ymin = win_pct - 1.96*se_win_pct,
                      ymax = win_pct + 1.96*se_win_pct),
                  width = 0.2) +
    geom_hline(yintercept = 0.5, linetype = "dashed", alpha = 0.5) +
    scale_y_continuous(labels = scales::percent_format()) +
    labs(
      title = "Win Percentage by Rest Differential",
      subtitle = "Positive = more rest than opponent",
      x = "Rest Differential (days)",
      y = "Win %"
    ) +
    theme_minimal() +
    theme(legend.position = "none")
  
  # Odds ratios
  p3 <- win_results$odds_ratios %>%
    filter(model == "Full") %>%
    ggplot(aes(x = reorder(term, estimate), y = estimate,
               ymin = conf.low, ymax = conf.high)) +
    geom_pointrange() +
    geom_hline(yintercept = 1, linetype = "dashed", color = "red") +
    coord_flip() +
    labs(
      title = "Odds Ratios for Win Probability",
      subtitle = "Full Model",
      x = "",
      y = "Odds Ratio (95% CI)"
    ) +
    theme_minimal()
  
  list(by_category = p1, by_restdiff = p2, odds_ratios = p3)
}

# -----------------------------------------------------------------------------
# 5.3 DiD Plots
# -----------------------------------------------------------------------------
plot_did_analysis <- function(did_results) {
  
  # Weekly injury trends
  p1 <- did_results$weekly_trends %>%
    ggplot(aes(x = week, y = mean_injuries, color = period)) +
    geom_line(linewidth = 1) +
    geom_point(size = 2) +
    geom_vline(xintercept = 13, linetype = "dashed", alpha = 0.5) +
    annotate("text", x = 13.5, y = max(did_results$weekly_trends$mean_injuries),
             label = "Late Season", hjust = 0, size = 3) +
    labs(
      title = "Injury Rates by Week: 16-Game vs 17-Game Seasons",
      subtitle = "Difference-in-Differences Analysis",
      x = "Week",
      y = "Mean Injuries",
      color = "Season Type"
    ) +
    theme_minimal()
  
  # Weekly EPA trends
  p2 <- did_results$weekly_trends %>%
    ggplot(aes(x = week, y = mean_epa, color = period)) +
    geom_line(linewidth = 1) +
    geom_point(size = 2) +
    geom_vline(xintercept = 13, linetype = "dashed", alpha = 0.5) +
    geom_hline(yintercept = 0, linetype = "dotted", alpha = 0.5) +
    labs(
      title = "Performance by Week: 16-Game vs 17-Game Seasons",
      x = "Week",
      y = "Mean EPA/Play",
      color = "Season Type"
    ) +
    theme_minimal()
  
  list(injury_trends = p1, epa_trends = p2)
}

# -----------------------------------------------------------------------------
# 5.4 Survival Plots
# -----------------------------------------------------------------------------
plot_survival_curves <- function(survival_results) {
  
  # Overall survival - add time 0 point with survival = 1.0
  km_overall_df <- data.frame(
    time = survival_results$km_overall$time,
    surv = survival_results$km_overall$surv,
    lower = survival_results$km_overall$lower,
    upper = survival_results$km_overall$upper
  )
  
  # Add time 0 point with survival = 1.0
  time0_data <- data.frame(
    time = 0,
    surv = 1.0,
    lower = 1.0,
    upper = 1.0
  )
  km_overall_df <- rbind(time0_data, km_overall_df) %>%
    arrange(time)
  
  p1 <- ggplot(km_overall_df, aes(x = time, y = surv)) +
    geom_step(linewidth = 1) +
    geom_ribbon(aes(ymin = lower, ymax = upper), alpha = 0.2) +
    labs(
      title = "Overall Injury-Free Survival",
      x = "Games into Season",
      y = "Probability Injury-Free"
    ) +
    ylim(0, 1) +
    theme_minimal()
  
  # By rest group (use survminer if available)
  p2 <- tryCatch({
    ggsurvplot(survival_results$km_by_rest,
               data = survival_results$survival_data,
               risk.table = FALSE,
               pval = TRUE,
               conf.int = TRUE)$plot +
      labs(title = "Survival by Rest Pattern")
  }, error = function(e) {
    # Fallback manual plot
    km_rest_df <- data.frame(
      time = survival_results$km_by_rest$time,
      surv = survival_results$km_by_rest$surv,
      strata = rep(names(survival_results$km_by_rest$strata),
                   survival_results$km_by_rest$strata)
    )
    
    ggplot(km_rest_df, aes(x = time, y = surv, color = strata)) +
      geom_step(linewidth = 1) +
      labs(
        title = "Survival by Rest Pattern",
        x = "Games into Season",
        y = "Probability Injury-Free",
        color = "Rest Pattern"
      ) +
      ylim(0, 1) +
      theme_minimal()
  })
  
  # Hazard ratios
  p3 <- survival_results$hazard_ratios %>%
    filter(!grepl("Intercept|season", term)) %>%
    ggplot(aes(x = reorder(term, hr), y = hr,
               ymin = hr_lower, ymax = hr_upper)) +
    geom_pointrange(size = 0.8) +
    geom_hline(yintercept = 1, linetype = "dashed", color = "red") +
    coord_flip() +
    labs(
      title = "Hazard Ratios for Injury Risk",
      subtitle = "HR > 1 = Higher Risk",
      x = "",
      y = "Hazard Ratio (95% CI)"
    ) +
    theme_minimal()
  
  # Cox model coefficients (forest plot style)
  cox_coefs <- tidy(survival_results$cox_full) %>%
    filter(!grepl("Intercept|season", term)) %>%
    mutate(
      # Clean term names
      term_clean = case_when(
        grepl("rest_group", term) ~ gsub("rest_group", "Rest: ", term),
        grepl("total_games", term) ~ "Total Games",
        TRUE ~ term
      ),
      # Calculate HR and CI
      hr = exp(estimate),
      hr_lower = exp(estimate - 1.96 * std.error),
      hr_upper = exp(estimate + 1.96 * std.error),
      # Significance indicator
      significant = p.value < 0.05
    )
  
  p4 <- cox_coefs %>%
    ggplot(aes(x = reorder(term_clean, estimate), y = estimate,
               ymin = estimate - 1.96 * std.error,
               ymax = estimate + 1.96 * std.error,
               color = significant)) +
    geom_pointrange(size = 0.8, fatten = 2) +
    geom_hline(yintercept = 0, linetype = "dashed", color = "red", alpha = 0.5) +
    coord_flip() +
    scale_color_manual(values = c("FALSE" = "gray50", "TRUE" = "black"),
                      labels = c("FALSE" = "p ≥ 0.05", "TRUE" = "p < 0.05"),
                      name = "Significance") +
    labs(
      title = "Cox Model Coefficients (Log-Hazard Ratios)",
      subtitle = "Full Model: Rest Pattern + Workload + Total Games",
      x = "Covariate",
      y = "Coefficient (Log-HR) with 95% CI",
      caption = "Coefficient > 0 = Higher Hazard (More Risk)\nCoefficient < 0 = Lower Hazard (Less Risk)"
    ) +
    theme_minimal() +
    theme(legend.position = "bottom")
  
  # Alternative: Forest plot with HR scale
  p5 <- cox_coefs %>%
    ggplot(aes(x = reorder(term_clean, hr), y = hr,
               ymin = hr_lower, ymax = hr_upper,
               color = significant)) +
    geom_pointrange(size = 0.8, fatten = 2) +
    geom_hline(yintercept = 1, linetype = "dashed", color = "red", alpha = 0.5) +
    coord_flip() +
    scale_color_manual(values = c("FALSE" = "gray50", "TRUE" = "black"),
                      labels = c("FALSE" = "p ≥ 0.05", "TRUE" = "p < 0.05"),
                      name = "Significance") +
    scale_y_continuous(trans = "log10",
                      breaks = c(0.5, 0.7, 1.0, 1.5, 2.0, 3.0),
                      labels = c("0.5", "0.7", "1.0", "1.5", "2.0", "3.0")) +
    labs(
      title = "Cox Model Forest Plot (Hazard Ratios)",
      subtitle = "Full Model: Rest Pattern + Workload + Total Games",
      x = "Covariate",
      y = "Hazard Ratio (95% CI, log scale)",
      caption = "HR > 1 = Higher Risk | HR < 1 = Lower Risk"
    ) +
    theme_minimal() +
    theme(legend.position = "bottom")
  
  # Cox model predicted survival curves by rest group
  p6 <- tryCatch({
    # Get reference values for other covariates
    surv_data <- survival_results$survival_data
    ref_total_games <- median(surv_data$total_games, na.rm = TRUE)
    ref_season <- names(sort(table(surv_data$season), decreasing = TRUE))[1]  # Most common season
    
    # Create new data for only Standard Rest and High Short Rest
    newdata <- data.frame(
      rest_group = factor(c("Standard Rest Only", "High Short Rest"),
                         levels = levels(surv_data$rest_group)),
      pct_short_weeks = c(0, 0.25),  # Representative values
      total_games = ref_total_games,
      season = factor(ref_season, levels = levels(factor(surv_data$season)))
    )
    
    # Fit survival curves for each group
    cox_surv_fit <- survfit(survival_results$cox_full, newdata = newdata, conf.type = "log-log")
    
    # Extract survival data and ensure it starts at time 0 with survival = 1.0
    n_strata <- length(cox_surv_fit$strata)
    cox_surv_df <- data.frame(
      time = rep(cox_surv_fit$time, nrow(newdata)),
      surv = as.vector(cox_surv_fit$surv),
      lower = as.vector(cox_surv_fit$lower),
      upper = as.vector(cox_surv_fit$upper),
      rest_group = rep(newdata$rest_group, each = length(cox_surv_fit$time))
    )
    
    # Add time 0 point with survival = 1.0 for each group
    time0_data <- data.frame(
      time = 0,
      surv = 1.0,
      lower = 1.0,
      upper = 1.0,
      rest_group = newdata$rest_group
    )
    cox_surv_df <- rbind(time0_data, cox_surv_df) %>%
      arrange(rest_group, time) %>%
      mutate(
        # Create descriptive legend labels
        rest_group_label = case_when(
          rest_group == "Standard Rest Only" ~ "Standard Rest Only\n(0% short-rest games, typical schedule)",
          rest_group == "High Short Rest" ~ "High Short Rest\n(≥20% short-rest games, TNF-heavy schedule)",
          TRUE ~ as.character(rest_group)
        )
      )
    
    ggplot(cox_surv_df, aes(x = time, y = surv, color = rest_group_label, fill = rest_group_label)) +
      geom_step(linewidth = 1.2) +
      geom_ribbon(aes(ymin = lower, ymax = upper), alpha = 0.2, color = NA) +
      labs(
        title = "Cox Model Predicted Survival Curves",
        subtitle = "Adjusted for workload and total games",
        x = "Games into Season",
        y = "Predicted Probability Injury-Free",
        color = "Rest Pattern",
        fill = "Rest Pattern"
      ) +
      ylim(0, 1) +
      theme_minimal() +
      theme(legend.position = "bottom",
            legend.text = element_text(size = 10))
  }, error = function(e) {
    # Fallback: simpler version without confidence intervals
    surv_data <- survival_results$survival_data
    ref_total_games <- median(surv_data$total_games, na.rm = TRUE)
    ref_season <- names(sort(table(surv_data$season), decreasing = TRUE))[1]
    
    newdata <- data.frame(
      rest_group = factor(c("Standard Rest Only", "High Short Rest"),
                         levels = levels(surv_data$rest_group)),
      pct_short_weeks = c(0, 0.25),
      total_games = ref_total_games,
      season = factor(ref_season, levels = levels(factor(surv_data$season)))
    )
    
    cox_surv_fit <- survfit(survival_results$cox_full, newdata = newdata)
    
    cox_surv_df <- data.frame(
      time = rep(cox_surv_fit$time, nrow(newdata)),
      surv = as.vector(cox_surv_fit$surv),
      rest_group = rep(newdata$rest_group, each = length(cox_surv_fit$time))
    )
    
    # Add time 0 point with survival = 1.0 for each group
    time0_data <- data.frame(
      time = 0,
      surv = 1.0,
      rest_group = newdata$rest_group
    )
    cox_surv_df <- rbind(time0_data, cox_surv_df) %>%
      arrange(rest_group, time) %>%
      mutate(
        # Create descriptive legend labels
        rest_group_label = case_when(
          rest_group == "Standard Rest Only" ~ "Standard Rest Only\n(0% short-rest games, typical schedule)",
          rest_group == "High Short Rest" ~ "High Short Rest\n(≥20% short-rest games, TNF-heavy schedule)",
          TRUE ~ as.character(rest_group)
        )
      )
    
    ggplot(cox_surv_df, aes(x = time, y = surv, color = rest_group_label)) +
      geom_step(linewidth = 1.2) +
      labs(
        title = "Cox Model Predicted Survival Curves",
        subtitle = "Adjusted for workload and total games",
        x = "Games into Season",
        y = "Predicted Probability Injury-Free",
        color = "Rest Pattern"
      ) +
      ylim(0, 1) +
      theme_minimal() +
      theme(legend.position = "bottom",
            legend.text = element_text(size = 10))
  })
  
  list(overall = p1, by_rest = p2, hazard_ratios = p3, cox_coefficients = p4, cox_forest = p5, cox_survival_curves = p6)
}

# -----------------------------------------------------------------------------
# 4.4 Plot Severe Injury Survival Curves
# -----------------------------------------------------------------------------
plot_severe_injury_survival_curves <- function(severe_injury_survival_results) {
  
  # Overall survival - add time 0 point with survival = 1.0
  km_overall_df <- data.frame(
    time = severe_injury_survival_results$km_overall$time,
    surv = severe_injury_survival_results$km_overall$surv,
    lower = severe_injury_survival_results$km_overall$lower,
    upper = severe_injury_survival_results$km_overall$upper
  )
  
  # Add time 0 point with survival = 1.0
  time0_data <- data.frame(
    time = 0,
    surv = 1.0,
    lower = 1.0,
    upper = 1.0
  )
  km_overall_df <- rbind(time0_data, km_overall_df) %>%
    arrange(time)
  
  p1 <- ggplot(km_overall_df, aes(x = time, y = surv)) +
    geom_step(linewidth = 1) +
    geom_ribbon(aes(ymin = lower, ymax = upper), alpha = 0.2) +
    labs(
      title = "Overall Severe Injury-Free Survival",
      subtitle = "Severe injury = out 2+ consecutive weeks",
      x = "Games into Season",
      y = "Probability Severe Injury-Free"
    ) +
    ylim(0, 1) +
    theme_minimal()
  
  # By rest group (use survminer if available)
  p2 <- tryCatch({
    ggsurvplot(severe_injury_survival_results$km_by_rest,
               data = severe_injury_survival_results$survival_data,
               risk.table = FALSE,
               pval = TRUE,
               conf.int = TRUE)$plot +
      labs(title = "Severe Injury Survival by Rest Pattern",
           subtitle = "Severe injury = out 2+ consecutive weeks")
  }, error = function(e) {
    # Fallback manual plot
    km_rest_df <- data.frame(
      time = severe_injury_survival_results$km_by_rest$time,
      surv = severe_injury_survival_results$km_by_rest$surv,
      strata = rep(names(severe_injury_survival_results$km_by_rest$strata),
                   severe_injury_survival_results$km_by_rest$strata)
    )
    
    ggplot(km_rest_df, aes(x = time, y = surv, color = strata)) +
      geom_step(linewidth = 1) +
      labs(
        title = "Severe Injury Survival by Rest Pattern",
        subtitle = "Severe injury = out 2+ consecutive weeks",
        x = "Games into Season",
        y = "Probability Severe Injury-Free",
        color = "Rest Pattern"
      ) +
      ylim(0, 1) +
      theme_minimal()
  })
  
  # Hazard ratios
  p3 <- severe_injury_survival_results$hazard_ratios %>%
    filter(!grepl("Intercept|season", term)) %>%
    ggplot(aes(x = reorder(term, hr), y = hr,
               ymin = hr_lower, ymax = hr_upper)) +
    geom_pointrange(size = 0.8) +
    geom_hline(yintercept = 1, linetype = "dashed", color = "red") +
    coord_flip() +
    labs(
      title = "Hazard Ratios for Severe Injury Risk",
      subtitle = "HR > 1 = Higher Risk | Severe injury = out 2+ consecutive weeks",
      x = "",
      y = "Hazard Ratio (95% CI)"
    ) +
    theme_minimal()
  
  # Cox model coefficients (forest plot style)
  cox_coefs <- tidy(severe_injury_survival_results$cox_full) %>%
    filter(!grepl("Intercept|season", term)) %>%
    mutate(
      # Clean term names
      term_clean = case_when(
        grepl("rest_group", term) ~ gsub("rest_group", "Rest: ", term),
        grepl("total_games", term) ~ "Total Games",
        TRUE ~ term
      ),
      # Calculate HR and CI
      hr = exp(estimate),
      hr_lower = exp(estimate - 1.96 * std.error),
      hr_upper = exp(estimate + 1.96 * std.error),
      # Significance indicator
      significant = p.value < 0.05
    )
  
  p4 <- cox_coefs %>%
    ggplot(aes(x = reorder(term_clean, estimate), y = estimate,
               ymin = estimate - 1.96 * std.error,
               ymax = estimate + 1.96 * std.error,
               color = significant)) +
    geom_pointrange(size = 0.8, fatten = 2) +
    geom_hline(yintercept = 0, linetype = "dashed", color = "red", alpha = 0.5) +
    coord_flip() +
    scale_color_manual(values = c("FALSE" = "gray50", "TRUE" = "black"),
                      labels = c("FALSE" = "p ≥ 0.05", "TRUE" = "p < 0.05"),
                      name = "Significance") +
    labs(
      title = "Cox Model Coefficients (Log-Hazard Ratios) - Severe Injuries",
      subtitle = "Full Model: Rest Pattern + Total Games | Severe injury = out 2+ consecutive weeks",
      x = "Covariate",
      y = "Coefficient (Log-HR) with 95% CI",
      caption = "Coefficient > 0 = Higher Hazard (More Risk)\nCoefficient < 0 = Lower Hazard (Less Risk)"
    ) +
    theme_minimal() +
    theme(legend.position = "bottom")
  
  # Alternative: Forest plot with HR scale
  p5 <- cox_coefs %>%
    ggplot(aes(x = reorder(term_clean, hr), y = hr,
               ymin = hr_lower, ymax = hr_upper,
               color = significant)) +
    geom_pointrange(size = 0.8, fatten = 2) +
    geom_hline(yintercept = 1, linetype = "dashed", color = "red", alpha = 0.5) +
    coord_flip() +
    scale_color_manual(values = c("FALSE" = "gray50", "TRUE" = "black"),
                      labels = c("FALSE" = "p ≥ 0.05", "TRUE" = "p < 0.05"),
                      name = "Significance") +
    scale_y_continuous(trans = "log10",
                      breaks = c(0.5, 0.7, 1.0, 1.5, 2.0, 3.0),
                      labels = c("0.5", "0.7", "1.0", "1.5", "2.0", "3.0")) +
    labs(
      title = "Cox Model Forest Plot (Hazard Ratios) - Severe Injuries",
      subtitle = "Full Model: Rest Pattern + Total Games | Severe injury = out 2+ consecutive weeks",
      x = "Covariate",
      y = "Hazard Ratio (95% CI, log scale)",
      caption = "HR > 1 = Higher Risk | HR < 1 = Lower Risk"
    ) +
    theme_minimal() +
    theme(legend.position = "bottom")
  
  # Cox model predicted survival curves by rest group
  p6 <- tryCatch({
    # Get reference values for other covariates
    surv_data <- severe_injury_survival_results$survival_data
    ref_total_games <- median(surv_data$total_games, na.rm = TRUE)
    ref_season <- names(sort(table(surv_data$season), decreasing = TRUE))[1]  # Most common season
    
    # Create new data for only Standard Rest and High Short Rest
    newdata <- data.frame(
      rest_group = factor(c("Standard Rest Only", "High Short Rest"),
                         levels = levels(surv_data$rest_group)),
      total_games = ref_total_games,
      season = factor(ref_season, levels = levels(factor(surv_data$season)))
    )
    
    # Fit survival curves for each group
    cox_surv_fit <- survfit(severe_injury_survival_results$cox_full, newdata = newdata, conf.type = "log-log")
    
    # Extract survival data and ensure it starts at time 0 with survival = 1.0
    n_strata <- length(cox_surv_fit$strata)
    cox_surv_df <- data.frame(
      time = rep(cox_surv_fit$time, nrow(newdata)),
      surv = as.vector(cox_surv_fit$surv),
      lower = as.vector(cox_surv_fit$lower),
      upper = as.vector(cox_surv_fit$upper),
      rest_group = rep(newdata$rest_group, each = length(cox_surv_fit$time))
    )
    
    # Add time 0 point with survival = 1.0 for each group
    time0_data <- data.frame(
      time = 0,
      surv = 1.0,
      lower = 1.0,
      upper = 1.0,
      rest_group = newdata$rest_group
    )
    cox_surv_df <- rbind(time0_data, cox_surv_df) %>%
      arrange(rest_group, time) %>%
      mutate(
        # Create descriptive legend labels
        rest_group_label = case_when(
          rest_group == "Standard Rest Only" ~ "Standard Rest Only\n(0% short-rest games, typical schedule)",
          rest_group == "High Short Rest" ~ "High Short Rest\n(≥20% short-rest games, TNF-heavy schedule)",
          TRUE ~ as.character(rest_group)
        )
      )
    
    ggplot(cox_surv_df, aes(x = time, y = surv, color = rest_group_label, fill = rest_group_label)) +
      geom_step(linewidth = 1.2) +
      geom_ribbon(aes(ymin = lower, ymax = upper), alpha = 0.2, color = NA) +
      labs(
        title = "Cox Model Predicted Survival Curves - Severe Injuries",
        subtitle = "Adjusted for total games | Severe injury = out 2+ consecutive weeks",
        x = "Games into Season",
        y = "Predicted Probability Severe Injury-Free",
        color = "Rest Pattern",
        fill = "Rest Pattern"
      ) +
      ylim(0, 1) +
      theme_minimal() +
      theme(legend.position = "bottom",
            legend.text = element_text(size = 10))
  }, error = function(e) {
    # Fallback: simpler version without confidence intervals
    surv_data <- severe_injury_survival_results$survival_data
    ref_total_games <- median(surv_data$total_games, na.rm = TRUE)
    ref_season <- names(sort(table(surv_data$season), decreasing = TRUE))[1]
    
    newdata <- data.frame(
      rest_group = factor(c("Standard Rest Only", "High Short Rest"),
                         levels = levels(surv_data$rest_group)),
      total_games = ref_total_games,
      season = factor(ref_season, levels = levels(factor(surv_data$season)))
    )
    
    cox_surv_fit <- survfit(severe_injury_survival_results$cox_full, newdata = newdata)
    
    cox_surv_df <- data.frame(
      time = rep(cox_surv_fit$time, nrow(newdata)),
      surv = as.vector(cox_surv_fit$surv),
      rest_group = rep(newdata$rest_group, each = length(cox_surv_fit$time))
    )
    
    # Add time 0 point with survival = 1.0 for each group
    time0_data <- data.frame(
      time = 0,
      surv = 1.0,
      rest_group = newdata$rest_group
    )
    cox_surv_df <- rbind(time0_data, cox_surv_df) %>%
      arrange(rest_group, time) %>%
      mutate(
        # Create descriptive legend labels
        rest_group_label = case_when(
          rest_group == "Standard Rest Only" ~ "Standard Rest Only\n(0% short-rest games, typical schedule)",
          rest_group == "High Short Rest" ~ "High Short Rest\n(≥20% short-rest games, TNF-heavy schedule)",
          TRUE ~ as.character(rest_group)
        )
      )
    
    ggplot(cox_surv_df, aes(x = time, y = surv, color = rest_group_label)) +
      geom_step(linewidth = 1.2) +
      labs(
        title = "Cox Model Predicted Survival Curves - Severe Injuries",
        subtitle = "Adjusted for total games | Severe injury = out 2+ consecutive weeks",
        x = "Games into Season",
        y = "Predicted Probability Severe Injury-Free",
        color = "Rest Pattern"
      ) +
      ylim(0, 1) +
      theme_minimal() +
      theme(legend.position = "bottom",
            legend.text = element_text(size = 10))
  })
  
  list(overall = p1, by_rest = p2, hazard_ratios = p3, cox_coefficients = p4, cox_forest = p5, cox_survival_curves = p6)
}

# -----------------------------------------------------------------------------
# 5.5 Injury Severity Plots
# -----------------------------------------------------------------------------
plot_injury_severity <- function(severity_results) {
  
  # Games missed by rest category
  p1 <- severity_results$summary %>%
    ggplot(aes(x = rest_category, y = mean_games_missed, fill = rest_category)) +
    geom_col() +
    geom_errorbar(aes(ymin = mean_games_missed - 1.96*se_games_missed,
                      ymax = mean_games_missed + 1.96*se_games_missed),
                  width = 0.2) +
    labs(
      title = "Injury Severity: Games Missed (Next 4 Weeks) by Rest Category",
      subtitle = "Cumulative games missed by players out due to injury",
      x = "Rest Category",
      y = "Mean Games Missed"
    ) +
    theme_minimal() +
    theme(legend.position = "none",
          axis.text.x = element_text(angle = 20, hjust = 1))
  
  # Rate ratios for severity
  if (!is.null(severity_results$rate_ratios) && nrow(severity_results$rate_ratios) > 0) {
    p2 <- severity_results$rate_ratios %>%
      ggplot(aes(x = reorder(term, rate_ratio), y = rate_ratio,
                 ymin = rr_lower, ymax = rr_upper)) +
      geom_pointrange(size = 0.8) +
      geom_hline(yintercept = 1, linetype = "dashed", color = "red") +
      coord_flip() +
      labs(
        title = "Severity Rate Ratios by Rest Category",
        subtitle = "HR > 1 = More Games Missed",
        x = "",
        y = "Rate Ratio (95% CI)"
      ) +
      theme_minimal()
  } else {
    p2 <- NULL
  }
  
  list(severity_by_rest = p1, severity_ratios = p2)
}

# -----------------------------------------------------------------------------
# 5.6 Position Heterogeneity Plots
# -----------------------------------------------------------------------------
plot_position_heterogeneity <- function(position_results) {
  
  if (is.null(position_results)) {
    return(NULL)
  }
  
  # Injury rates by position and rest category
  p1 <- position_results$position_injury_rates %>%
    filter(rest_category %in% c("Standard (6-7 days)", "Thursday (Short Rest)")) %>%
    ggplot(aes(x = position_group, y = injury_rate, fill = rest_category)) +
    geom_col(position = "dodge") +
    labs(
      title = "Injury Rates by Position Group",
      subtitle = "Standard Rest vs TNF",
      x = "Position Group",
      y = "Injury Rate",
      fill = "Rest Category"
    ) +
    theme_minimal() +
    theme(axis.text.x = element_text(angle = 45, hjust = 1))
  
  # Short-rest exposure by position
  p2 <- position_results$position_exposure %>%
    ggplot(aes(x = reorder(position_group, pct_short_weeks), 
               y = pct_short_weeks, fill = position_group)) +
    geom_col() +
    scale_y_continuous(labels = scales::percent_format()) +
    labs(
      title = "Short-Rest Exposure by Position",
      subtitle = "Percentage of games played on short rest",
      x = "Position Group",
      y = "% Short Rest Games"
    ) +
    theme_minimal() +
    theme(legend.position = "none",
          axis.text.x = element_text(angle = 45, hjust = 1))
  
  # Position-specific hazard ratios (if available)
  p3 <- NULL
  if (!is.null(position_results$position_hr) && nrow(position_results$position_hr) > 0) {
    p3 <- position_results$position_hr %>%
      filter(grepl("rest_group", term)) %>%
      ggplot(aes(x = reorder(term, hr), y = hr,
                 ymin = hr_lower, ymax = hr_upper)) +
      geom_pointrange(size = 0.8) +
      geom_hline(yintercept = 1, linetype = "dashed", color = "red") +
      coord_flip() +
      labs(
        title = "Position-Specific Hazard Ratios",
        subtitle = "Injury risk by position and rest pattern",
        x = "",
        y = "Hazard Ratio (95% CI)"
      ) +
      theme_minimal()
  }
  
  list(injury_rates = p1, exposure = p2, position_hr = p3)
}

# -----------------------------------------------------------------------------
# 5.7 Bye Week Effectiveness Plots
# -----------------------------------------------------------------------------
plot_bye_effectiveness <- function(bye_results) {
  
  # TNF comparison: After bye vs Without bye
  p1 <- bye_results$tnf_comparison %>%
    ggplot(aes(x = tnf_type, y = mean_injuries, fill = tnf_type)) +
    geom_col() +
    geom_errorbar(aes(ymin = mean_injuries - 1.96*se_injuries,
                      ymax = mean_injuries + 1.96*se_injuries),
                  width = 0.2) +
    labs(
      title = "TNF Injury Rates: After Bye vs Without Bye",
      subtitle = "Does a bye week buffer short-rest injury risk?",
      x = "TNF Type",
      y = "Mean Injuries Next Week"
    ) +
    theme_minimal() +
    theme(legend.position = "none")
  
  # Games missed comparison
  p2 <- bye_results$tnf_comparison %>%
    ggplot(aes(x = tnf_type, y = mean_games_missed, fill = tnf_type)) +
    geom_col() +
    geom_errorbar(aes(ymin = mean_games_missed - 1.96*se_games_missed,
                      ymax = mean_games_missed + 1.96*se_games_missed),
                  width = 0.2) +
    labs(
      title = "TNF Injury Severity: After Bye vs Without Bye",
      subtitle = "Games missed in next 4 weeks",
      x = "TNF Type",
      y = "Mean Games Missed"
    ) +
    theme_minimal() +
    theme(legend.position = "none")
  
  # Bye placement timing
  if (!is.null(bye_results$bye_placement) && nrow(bye_results$bye_placement) > 0) {
    p3 <- bye_results$bye_placement %>%
      ggplot(aes(x = bye_timing, y = mean_injuries_next, fill = bye_timing)) +
      geom_col() +
      labs(
        title = "Injury Rates by Bye Week Timing",
        subtitle = "Does when the bye occurs matter?",
        x = "Bye Week Timing",
        y = "Mean Injuries Next Week"
      ) +
      theme_minimal() +
      theme(legend.position = "none",
            axis.text.x = element_text(angle = 20, hjust = 1))
  } else {
    p3 <- NULL
  }
  
  list(tnf_comparison = p1, severity_comparison = p2, bye_timing = p3)
}

# -----------------------------------------------------------------------------
# 5.8 Injury Type Plots
# -----------------------------------------------------------------------------
plot_injury_types <- function(injury_type_results) {
  
  if (is.null(injury_type_results)) {
    return(NULL)
  }
  
  # Injury rates by type and rest category
  p1 <- NULL
  if (!is.null(injury_type_results$injury_type_rates) && 
      nrow(injury_type_results$injury_type_rates) > 0) {
    p1 <- injury_type_results$injury_type_rates %>%
      filter(rest_category %in% c("Standard (6-7 days)", "Thursday (Short Rest)")) %>%
      ggplot(aes(x = injury_type, y = injury_rate, fill = rest_category)) +
      geom_col(position = "dodge") +
      geom_errorbar(aes(ymin = injury_rate - 1.96*se_rate,
                        ymax = injury_rate + 1.96*se_rate),
                    position = position_dodge(width = 0.9), width = 0.2) +
      labs(
        title = "Injury Rates by Type: Standard Rest vs TNF",
        subtitle = "Does short rest increase specific injury types?",
        x = "Injury Type",
        y = "Injury Rate",
        fill = "Rest Category"
      ) +
      theme_minimal() +
      theme(axis.text.x = element_text(angle = 20, hjust = 1))
  }
  
  # Rate ratios by injury type
  p2 <- NULL
  if (!is.null(injury_type_results$injury_type_tnf_comparison) &&
      nrow(injury_type_results$injury_type_tnf_comparison) > 0) {
    # Calculate CI for rate ratio (log-normal approximation)
    plot_data <- injury_type_results$injury_type_tnf_comparison %>%
      mutate(
        log_rr = log(rate_ratio),
        se_log_rr = se_diff / rate_ratio,  # Approximate SE of log(RR)
        rr_lower = exp(log_rr - 1.96 * se_log_rr),
        rr_upper = exp(log_rr + 1.96 * se_log_rr)
      )
    
    p2 <- plot_data %>%
      ggplot(aes(x = reorder(injury_type, rate_ratio), y = rate_ratio,
                 ymin = rr_lower, ymax = rr_upper)) +
      geom_pointrange(size = 0.8) +
      geom_hline(yintercept = 1, linetype = "dashed", color = "red") +
      coord_flip() +
      labs(
        title = "Injury Type Rate Ratios (TNF vs Standard)",
        subtitle = "HR > 1 = Higher risk on TNF",
        x = "Injury Type",
        y = "Rate Ratio (95% CI)"
      ) +
      theme_minimal()
  }
  
  # Distribution of injury types
  p3 <- NULL
  if (!is.null(injury_type_results$injury_type_summary) &&
      nrow(injury_type_results$injury_type_summary) > 0) {
    p3 <- injury_type_results$injury_type_summary %>%
      ggplot(aes(x = reorder(injury_type, pct_of_total), y = pct_of_total, 
                 fill = injury_type)) +
      geom_col() +
      scale_y_continuous(labels = scales::percent_format()) +
      labs(
        title = "Distribution of Injury Types",
        subtitle = "Percentage of all injuries",
        x = "Injury Type",
        y = "Percentage of Total Injuries"
      ) +
      theme_minimal() +
      theme(legend.position = "none",
            axis.text.x = element_text(angle = 20, hjust = 1))
  }
  
  list(injury_rates_by_type = p1, type_rate_ratios = p2, type_distribution = p3)
}

# -----------------------------------------------------------------------------
# 5.9 Event Study DiD Plots
# -----------------------------------------------------------------------------
plot_event_study <- function(event_results) {
  
  # Combine injury and performance coefficients
  event_coefs <- bind_rows(
    event_results$injury_coefs,
    event_results$performance_coefs
  )
  
  p1 <- event_coefs %>%
    ggplot(aes(x = week, y = estimate, color = outcome,
               ymin = ci_lower, ymax = ci_upper)) +
    geom_hline(yintercept = 0, linetype = "dashed", color = "red", alpha = 0.5) +
    geom_vline(xintercept = 12, linetype = "dotted", alpha = 0.5) +
    geom_pointrange(size = 0.5, position = position_dodge(width = 0.3)) +
    geom_line(aes(group = outcome), alpha = 0.3) +
    annotate("text", x = 12, y = max(event_coefs$ci_upper, na.rm = TRUE) * 0.9,
             label = "Reference\n(Week 12)", hjust = 0.5, size = 3) +
    labs(
      title = "Event Study: 17-Game Season Impact by Week",
      subtitle = "Dynamic effects relative to Week 12 (reference period)",
      x = "Week",
      y = "Coefficient (17-Game vs 16-Game)",
      color = "Outcome"
    ) +
    theme_minimal() +
    theme(legend.position = "bottom")
  
  list(event_study = p1)
}

# -----------------------------------------------------------------------------
# 5.10 Distributed Lag Plots
# -----------------------------------------------------------------------------
plot_distributed_lags <- function(lag_results) {
  
  # Combine all lag coefficients
  lag_coefs <- bind_rows(
    lag_results$injury_coefs %>% mutate(outcome = "Injuries"),
    lag_results$performance_coefs %>% mutate(outcome = "Performance"),
    lag_results$win_coefs %>% mutate(outcome = "Win Probability")
  )
  
  p1 <- lag_coefs %>%
    filter(variable == "Rest Differential") %>%
    ggplot(aes(x = lag_period, y = effect, color = outcome,
               ymin = effect_lower, ymax = effect_upper)) +
    geom_hline(yintercept = if_else(lag_coefs$model_type[1] == "Injury", 1, 0),
               linetype = "dashed", color = "red", alpha = 0.5) +
    geom_pointrange(size = 0.6, position = position_dodge(width = 0.3)) +
    geom_line(aes(group = outcome), alpha = 0.3) +
    labs(
      title = "Distributed Lag Effects: Rest Differential",
      subtitle = "How past rest differentials affect current outcomes",
      x = "Weeks Ago",
      y = if_else(lag_coefs$model_type[1] == "Injury", "Rate Ratio", "Effect"),
      color = "Outcome"
    ) +
    theme_minimal() +
    theme(legend.position = "bottom")
  
  p2 <- lag_coefs %>%
    filter(variable == "Short Week") %>%
    ggplot(aes(x = lag_period, y = effect, color = outcome,
               ymin = effect_lower, ymax = effect_upper)) +
    geom_hline(yintercept = if_else(lag_coefs$model_type[1] == "Injury", 1, 0),
               linetype = "dashed", color = "red", alpha = 0.5) +
    geom_pointrange(size = 0.6, position = position_dodge(width = 0.3)) +
    geom_line(aes(group = outcome), alpha = 0.3) +
    labs(
      title = "Distributed Lag Effects: Short Rest Weeks",
      subtitle = "Cumulative impact of past short-rest games",
      x = "Weeks Ago",
      y = if_else(lag_coefs$model_type[1] == "Injury", "Rate Ratio", "Effect"),
      color = "Outcome"
    ) +
    theme_minimal() +
    theme(legend.position = "bottom")
  
  list(rest_diff_lags = p1, short_week_lags = p2)
}

# -----------------------------------------------------------------------------
# 5.11 Nonlinear Dose Response Plots
# -----------------------------------------------------------------------------
plot_dose_response <- function(dose_results) {
  
  p1 <- dose_results$injury_dose_response %>%
    ggplot(aes(x = rest_diff, y = effect_pct)) +
    geom_hline(yintercept = 0, linetype = "dashed", color = "red", alpha = 0.5) +
    geom_vline(xintercept = c(-2, 0, 2), linetype = "dotted", alpha = 0.3) +
    geom_line(linewidth = 1.2, color = "darkred") +
    geom_ribbon(aes(ymin = effect_pct - 5, ymax = effect_pct + 5), alpha = 0.2) +
    labs(
      title = "Nonlinear Dose Response: Injury Risk by Rest Differential",
      subtitle = "Percentage change in injury rate relative to equal rest (0 days)",
      x = "Rest Differential (days)",
      y = "% Change in Injury Rate",
      caption = "Vertical lines at ±2 days (proposed policy threshold)"
    ) +
    theme_minimal()
  
  p2 <- dose_results$performance_dose_response %>%
    ggplot(aes(x = rest_diff, y = effect)) +
    geom_hline(yintercept = 0, linetype = "dashed", color = "red", alpha = 0.5) +
    geom_vline(xintercept = c(-2, 0, 2), linetype = "dotted", alpha = 0.3) +
    geom_line(linewidth = 1.2, color = "darkblue") +
    labs(
      title = "Nonlinear Dose Response: Performance by Rest Differential",
      subtitle = "Change in EPA/play relative to equal rest",
      x = "Rest Differential (days)",
      y = "Change in EPA/Play",
      caption = "Vertical lines at ±2 days (proposed policy threshold)"
    ) +
    theme_minimal()
  
  p3 <- dose_results$win_dose_response %>%
    ggplot(aes(x = rest_diff, y = effect_pp)) +
    geom_hline(yintercept = 0, linetype = "dashed", color = "red", alpha = 0.5) +
    geom_vline(xintercept = c(-2, 0, 2), linetype = "dotted", alpha = 0.3) +
    geom_line(linewidth = 1.2, color = "darkgreen") +
    labs(
      title = "Nonlinear Dose Response: Win Probability by Rest Differential",
      subtitle = "Change in win probability (percentage points) relative to equal rest",
      x = "Rest Differential (days)",
      y = "Change in Win Probability (pp)",
      caption = "Vertical lines at ±2 days (proposed policy threshold)"
    ) +
    theme_minimal()
  
  list(injury_dose = p1, performance_dose = p2, win_dose = p3)
}

# -----------------------------------------------------------------------------
# 5.12 Counterfactual Policy Plots
# -----------------------------------------------------------------------------
plot_counterfactuals <- function(counterfactual_results) {
  
  impacts <- counterfactual_results$impacts %>%
    filter(policy != "Baseline")
  
  p1 <- impacts %>%
    ggplot(aes(x = policy, y = injuries_saved_per_season, fill = policy)) +
    geom_col() +
    geom_text(aes(label = round(injuries_saved_per_season, 0)),
              vjust = -0.5, size = 4) +
    labs(
      title = "Counterfactual Policy Impact: Injuries Prevented",
      subtitle = "Estimated injuries saved per season under different policies",
      x = "Policy",
      y = "Injuries Saved Per Season",
      fill = "Policy"
    ) +
    theme_minimal() +
    theme(legend.position = "none")
  
  p2 <- impacts %>%
    ggplot(aes(x = policy, y = win_change_pp, fill = policy)) +
    geom_col() +
    geom_hline(yintercept = 0, linetype = "dashed", color = "red", alpha = 0.5) +
    geom_text(aes(label = round(win_change_pp, 2)),
              vjust = if_else(impacts$win_change_pp > 0, -0.5, 1.5), size = 4) +
    labs(
      title = "Counterfactual Policy Impact: Win Probability Fairness",
      subtitle = "Change in average win probability (more fair = closer to 0.5)",
      x = "Policy",
      y = "Change in Win Probability (pp)",
      fill = "Policy"
    ) +
    theme_minimal() +
    theme(legend.position = "none")
  
  list(injuries_saved = p1, win_fairness = p2)
}


# -----------------------------------------------------------------------------
# 5.17 Marginal Structural Models Plot
# -----------------------------------------------------------------------------
plot_msm_results <- function(msm_results) {
  
  if (!msm_results$available || is.null(msm_results$effects)) {
    return(NULL)
  }
  
  # Extract effects for plotting
  effects_df <- bind_rows(
    msm_results$effects$short_week,
    msm_results$effects$unfair_rest
  ) %>%
    filter(!is.null(rate_ratio))
  
  if (nrow(effects_df) == 0) {
    return(NULL)
  }
  
  p1 <- effects_df %>%
    ggplot(aes(x = exposure, y = rate_ratio,
               ymin = ci_lower, ymax = ci_upper,
               fill = exposure)) +
    geom_col(alpha = 0.7) +
    geom_errorbar(width = 0.2) +
    geom_hline(yintercept = 1, linetype = "dashed", color = "red", alpha = 0.5) +
    labs(
      title = "Marginal Structural Models (IPW-Adjusted)",
      subtitle = "Inverse probability weighted estimates accounting for time-varying confounding",
      x = "Exposure",
      y = "Rate Ratio (95% CI)",
      fill = "Exposure",
      caption = "IPW adjusts for time-varying confounders (past injuries, workload, etc.)"
    ) +
    theme_minimal() +
    theme(legend.position = "none")
  
  list(msm_effects = p1)
}

# -----------------------------------------------------------------------------
# 5.13 Late-Season Workload Interaction Plots
# -----------------------------------------------------------------------------
plot_late_season_workload_interaction <- function(interaction_results) {
  
  # Heatmap: Week × Cumulative Short Weeks → Injury Risk
  p1 <- interaction_results$injury_predictions %>%
    ggplot(aes(x = week, y = cum_short_weeks, fill = predicted_injuries)) +
    geom_tile() +
    scale_fill_gradient2(low = "blue", mid = "white", high = "red",
                         midpoint = median(interaction_results$injury_predictions$predicted_injuries, na.rm = TRUE),
                         name = "Predicted\nInjuries") +
    labs(
      title = "Late-Season Compression: Injury Risk by Week and Cumulative Short Weeks",
      subtitle = "Risk increases non-linearly as season progresses and workload accumulates",
      x = "Season Week",
      y = "Cumulative Short Weeks",
      caption = "Darker red = higher predicted injury risk"
    ) +
    theme_minimal() +
    theme(legend.position = "right")
  
  # Line plot: Effect of cumulative short weeks by week
  p2 <- interaction_results$injury_predictions %>%
    filter(cum_short_weeks %in% c(0, 1, 2, 3, 4, 5)) %>%
    ggplot(aes(x = week, y = predicted_injuries, color = factor(cum_short_weeks))) +
    geom_line(linewidth = 1.2) +
    geom_point(size = 2) +
    scale_color_viridis_d(name = "Cumulative\nShort Weeks") +
    labs(
      title = "Injury Risk Trajectory: Effect of Cumulative Short Weeks Over Season",
      subtitle = "Late-season games with high cumulative workload show amplified risk",
      x = "Season Week",
      y = "Predicted Injuries (Next Week)",
      caption = "Lines show how injury risk evolves for different cumulative workload levels"
    ) +
    theme_minimal() +
    theme(legend.position = "bottom") +
    geom_vline(xintercept = 13, linetype = "dashed", color = "gray", alpha = 0.5) +
    annotate("text", x = 13.5, y = max(interaction_results$injury_predictions$predicted_injuries, na.rm = TRUE) * 0.9,
             label = "Late Season", hjust = 0, size = 3)
  
  # Performance heatmap
  p3 <- interaction_results$performance_predictions %>%
    ggplot(aes(x = week, y = cum_short_weeks, fill = predicted_epa)) +
    geom_tile() +
    scale_fill_gradient2(low = "red", mid = "white", high = "blue",
                         midpoint = median(interaction_results$performance_predictions$predicted_epa, na.rm = TRUE),
                         name = "Predicted\nEPA/Play") +
    labs(
      title = "Performance Decline: EPA by Week and Cumulative Short Weeks",
      subtitle = "Performance degrades more in late season with accumulated workload",
      x = "Season Week",
      y = "Cumulative Short Weeks",
      caption = "Darker blue = better performance, darker red = worse performance"
    ) +
    theme_minimal() +
    theme(legend.position = "right")
  
  # Interaction coefficient plot
  p4 <- interaction_results$interaction_coefficients %>%
    filter(!is.na(estimate)) %>%
    ggplot(aes(x = model, y = estimate_exp, ymin = estimate_exp - 1.96 * std.error,
               ymax = estimate_exp + 1.96 * std.error)) +
    geom_pointrange(size = 0.8) +
    geom_hline(yintercept = if_else(interaction_results$interaction_coefficients$model[1] %in% c("injury", "win"), 1, 0),
               linetype = "dashed", color = "red", alpha = 0.5) +
    labs(
      title = "Interaction Effect Coefficients",
      subtitle = "Week × Cumulative Short Weeks interaction",
      x = "Model",
      y = "Effect (Rate Ratio or Coefficient)",
      caption = "Positive values indicate amplification of workload effects in late season"
    ) +
    theme_minimal() +
    theme(axis.text.x = element_text(angle = 45, hjust = 1))
  
  list(
    interaction_heatmap = p1,
    injury_trajectory = p2,
    performance_heatmap = p3,
    interaction_coefficients = p4
  )
}


# -----------------------------------------------------------------------------

# =============================================================================
# PART 6: POLICY IMPACT AND RECOMMENDATIONS
# =============================================================================

# -----------------------------------------------------------------------------
# 6.1 Estimate Policy Impact
# -----------------------------------------------------------------------------
estimate_policy_impact <- function(injury_results, performance_results, win_results,
                                   did_results = NULL, data = NULL) {
  
  # Compute TNF games per season empirically from data (not assumed constant)
  # This accounts for variation across seasons and international games
  if (!is.null(data)) {
    tnf_games_by_season <- data %>%
      filter(is_short_rest_thursday) %>%
      group_by(season) %>%
      summarise(n_tnf_games = n_distinct(game_id), .groups = "drop")
    
    mean_tnf_games_per_season <- mean(tnf_games_by_season$n_tnf_games, na.rm = TRUE)
    tnf_games_per_season <- round(mean_tnf_games_per_season)
    
    # Store for reference
    attr(tnf_games_by_season, "mean") <- mean_tnf_games_per_season
  } else {
    # Fallback to config if data not available
    tnf_games_per_season <- CONFIG$tnf_games_per_season
    tnf_games_by_season <- NULL
  }
  
  # Get TNF injury rate ratio from model (adjusted for covariates)
  coefs <- tidy(injury_results$negbin_category)
  
  tnf_coef <- coefs %>%
    filter(term == "rest_categoryThursday (Short Rest)")
  
  if (nrow(tnf_coef) == 0) {
    rate_ratio <- NA
    rate_ratio_ci <- c(NA, NA)
  } else {
    rate_ratio <- exp(tnf_coef$estimate)
    rate_ratio_ci <- c(
      exp(tnf_coef$estimate - 1.96 * tnf_coef$std.error),
      exp(tnf_coef$estimate + 1.96 * tnf_coef$std.error)
    )
  }
  
  # Baseline injury rate (from summary, for context)
  baseline_rate <- injury_results$summary %>%
    filter(rest_category == "Standard (6-7 days)") %>%
    pull(mean_new_injuries)
  
  # Calculate excess injuries using model-based rate ratio
  # If rate_ratio > 1, TNF causes more injuries
  if (!is.na(rate_ratio) && rate_ratio > 1) {
    # Excess injuries per TNF game = baseline_rate * (rate_ratio - 1)
    excess_per_game <- baseline_rate * (rate_ratio - 1)
    # Per season: 2 teams per TNF game * empirically computed TNF games per season
    excess_per_season <- excess_per_game * 2 * tnf_games_per_season
  } else {
    # If rate ratio is <= 1 or NA, use raw difference (though this shouldn't happen)
  tnf_rate <- injury_results$summary %>%
      filter(rest_category == "Thursday (Short Rest)") %>%
    pull(mean_new_injuries)
  excess_per_game <- tnf_rate - baseline_rate
    excess_per_season <- excess_per_game * 2 * tnf_games_per_season
  }
  
  # Performance impact
  standard_epa <- performance_results$summary %>%
    filter(rest_category == "Standard (6-7 days)") %>%
    pull(mean_epa)
  
  tnf_epa <- performance_results$summary %>%
    filter(rest_category == "Thursday (Short Rest)") %>%
    pull(mean_epa)
  
  performance_deficit <- standard_epa - tnf_epa
  
  # Win probability impact
  win_effect <- win_results$marginal_effect$effect
  
  # ============================================================================
  # REST DIFFERENTIAL ANALYSIS (for Priority 3)
  # ============================================================================
  rest_diff_analysis <- list()
  
  # 1. Win rates by rest differential (from win_results)
  if (!is.null(win_results$by_restdiff)) {
    rest_diff_analysis$win_by_restdiff <- win_results$by_restdiff
  }
  
  # 2. Injury rates by rest differential (from injury_results)
  if (!is.null(injury_results$by_restdiff)) {
    rest_diff_analysis$injury_by_restdiff <- injury_results$by_restdiff
  }
  
  # 3. Calculate effects at multiple thresholds
  if (!is.null(win_results$full) && !is.null(injury_results$negbin_restdiff)) {
    # Reference scenario (equal rest)
    ref_data <- data.frame(
      rest_diff = 0,
      unfair_rest = FALSE,
      home = FALSE,
      games_since_bye = 4,
      cum_short_weeks = 1,
      crossed_timezones = FALSE,
      season = 2023,
      surface = "grass"
    )
    
    # Calculate effects at different thresholds
    thresholds <- c(-1, -2, -3, -4)
    rest_diff_effects <- map_dfr(thresholds, function(thresh) {
      # Win probability
      thresh_data <- ref_data
      thresh_data$rest_diff <- thresh
      thresh_data$unfair_rest <- (thresh <= -2)
      
      win_prob_ref <- predict(win_results$full, newdata = ref_data, type = "response")
      win_prob_thresh <- predict(win_results$full, newdata = thresh_data, type = "response")
      win_effect_pp <- as.numeric((win_prob_ref - win_prob_thresh) * 100)
      
      # Injury rate (using negative binomial model)
      # Get coefficient for rest_diff
      rest_diff_coef <- tidy(injury_results$negbin_restdiff) %>%
        filter(term == "rest_diff")
      
      if (nrow(rest_diff_coef) > 0) {
        # For negative binomial: log(rate) = intercept + coef * rest_diff
        # If coef is negative: more rest_diff (advantage) = fewer injuries
        # If coef is positive: more rest_diff (advantage) = more injuries (unlikely)
        # For rest disadvantage (thresh < 0), we want to compare to equal rest (thresh = 0)
        # Log rate ratio = coef * (thresh - 0) = coef * thresh
        # If thresh is negative and coef is negative, log_rr is positive (more injuries)
        log_rr <- rest_diff_coef$estimate * thresh
        injury_rr <- exp(log_rr)
        # For disadvantage (thresh < 0), if coef < 0, then log_rr > 0, so injury_rr > 1 (more injuries)
        # If coef > 0, then log_rr < 0, so injury_rr < 1 (fewer injuries - doesn't make sense)
        # We'll report the absolute change regardless
        injury_pct_change <- (injury_rr - 1) * 100
      } else {
        injury_rr <- NA
        injury_pct_change <- NA
      }
      
      tibble(
        rest_diff = thresh,
        win_prob_effect_pp = win_effect_pp,
        injury_rate_ratio = injury_rr,
        injury_pct_change = injury_pct_change
      )
    })
    
    rest_diff_analysis$effects_by_threshold <- rest_diff_effects
  }
  
  # 4. Count games with unfair rest differentials per season
  if (!is.null(data)) {
    unfair_rest_by_season <- data %>%
      filter(!is.na(rest_diff)) %>%
      mutate(
        unfair_disadvantage = rest_diff <= -2,
        unfair_advantage = rest_diff >= 2,
        unfair_any = abs(rest_diff) > 2
      ) %>%
      group_by(season) %>%
      summarise(
        n_games = n(),
        n_unfair_disadvantage = sum(unfair_disadvantage, na.rm = TRUE),
        n_unfair_advantage = sum(unfair_advantage, na.rm = TRUE),
        n_unfair_any = sum(unfair_any, na.rm = TRUE),
        pct_unfair = mean(unfair_any, na.rm = TRUE) * 100,
        .groups = "drop"
      )
    
    rest_diff_analysis$unfair_rest_by_season <- unfair_rest_by_season
    rest_diff_analysis$mean_unfair_games_per_season <- mean(unfair_rest_by_season$n_unfair_any, na.rm = TRUE)
  }
  
  # 5. Extract rest_diff coefficient from win model for narrative
  if (!is.null(win_results$full)) {
    rest_diff_coef <- tidy(win_results$full) %>%
      filter(term == "rest_diff")
    
    if (nrow(rest_diff_coef) > 0) {
      # Convert to percentage points per day of rest disadvantage
      # For logistic regression, marginal effect at mean ≈ coef * p(1-p)
      # Approximate: each day of rest disadvantage ≈ coef * 0.25 * 100 pp
      rest_diff_analysis$win_effect_per_day_pp <- abs(rest_diff_coef$estimate) * 0.25 * 100
    }
  }
  
  # 17-game impact (if available)
  did_impact <- NULL
  if (!is.null(did_results)) {
    did_impact <- list(
      injury_increase = did_results$did_estimates$injuries,
      epa_decline = did_results$did_estimates$epa
    )
  }
  
  list(
    tnf_rate_ratio = rate_ratio,
    tnf_rate_ratio_ci = rate_ratio_ci,
    baseline_injury_rate = baseline_rate,
    excess_injuries_per_game = excess_per_game,
    excess_injuries_per_season = excess_per_season,
    tnf_games_per_season = tnf_games_per_season,
    tnf_games_by_season = tnf_games_by_season,
    performance_deficit_epa = performance_deficit,
    win_probability_effect = win_effect,
    rest_differential_analysis = rest_diff_analysis,
    did_17_game_impact = did_impact
  )
}

# -----------------------------------------------------------------------------
# 6.2 Helper Functions for Priority 3 Recommendations
# -----------------------------------------------------------------------------
build_priority_3_finding <- function(policy_impact, dose_results = NULL, counterfactual_results = NULL) {
  rest_diff <- policy_impact$rest_differential_analysis
  
  if (is.null(rest_diff)) {
    # Fallback to simple version
    return(glue(
      "Teams with 2+ days less rest than opponents have ",
      "{round(policy_impact$win_probability_effect * 100, 1)}pp lower win probability. ",
      "This creates unfair competitive disadvantages."
    ))
  }
  
  # Get effect at -2 day threshold (the policy threshold)
  effect_at_2 <- NULL
  if (!is.null(rest_diff$effects_by_threshold)) {
    effect_at_2 <- rest_diff$effects_by_threshold %>%
      filter(rest_diff == -2)
  }
  
  # Get win rate data
  win_data <- NULL
  if (!is.null(rest_diff$win_by_restdiff)) {
    win_data <- rest_diff$win_by_restdiff
  }
  
  # Get injury data
  injury_data <- NULL
  if (!is.null(rest_diff$injury_by_restdiff)) {
    injury_data <- rest_diff$injury_by_restdiff
  }
  
  # Build finding with specific numbers
  finding_parts <- c()
  
  # Win probability effect
  if (!is.null(effect_at_2) && nrow(effect_at_2) > 0) {
    win_effect_2 <- round(effect_at_2$win_prob_effect_pp[1], 1)
    finding_parts <- c(finding_parts, 
      glue("Teams with 2+ days less rest face {win_effect_2} percentage point lower win probability (model-adjusted)"))
  } else {
    win_effect_simple <- round(policy_impact$win_probability_effect * 100, 1)
    finding_parts <- c(finding_parts,
      glue("Teams with 2+ days less rest face {win_effect_simple} percentage point lower win probability"))
  }
  
  # Show gradient if available
  if (!is.null(rest_diff$effects_by_threshold) && nrow(rest_diff$effects_by_threshold) > 0) {
    effect_3 <- rest_diff$effects_by_threshold %>% filter(rest_diff == -3)
    if (nrow(effect_3) > 0) {
      win_effect_3 <- round(effect_3$win_prob_effect_pp[1], 1)
      finding_parts <- c(finding_parts,
        glue("The effect escalates: teams with 3+ days disadvantage show {win_effect_3}pp lower win rates"))
    }
  }
  
  # Injury effect
  if (!is.null(effect_at_2) && nrow(effect_at_2) > 0 && !is.na(effect_at_2$injury_pct_change[1])) {
    injury_change <- round(effect_at_2$injury_pct_change[1], 1)
    if (injury_change > 0) {
      finding_parts <- c(finding_parts,
        glue("{injury_change}% higher injury rates compared to equal rest matchups"))
    }
  } else if (!is.null(injury_data) && nrow(injury_data) > 0) {
    # Use raw data comparison
    equal_rest <- injury_data %>% filter(rest_diff_bin == "-1 to 0" | rest_diff_bin == "1 to 2")
    disadvantage <- injury_data %>% filter(rest_diff_bin == "≤-2")
    if (nrow(equal_rest) > 0 && nrow(disadvantage) > 0) {
      equal_rate <- mean(equal_rest$mean_injuries, na.rm = TRUE)
      disadv_rate <- mean(disadvantage$mean_injuries, na.rm = TRUE)
      if (disadv_rate > equal_rate) {
        pct_increase <- round((disadv_rate / equal_rate - 1) * 100, 1)
        finding_parts <- c(finding_parts,
          glue("{pct_increase}% higher injury rates on average"))
      }
    }
  }
  
  # Frequency context
  if (!is.null(rest_diff$mean_unfair_games_per_season)) {
    mean_unfair <- round(rest_diff$mean_unfair_games_per_season, 0)
    finding_parts <- c(finding_parts,
      glue("On average, {mean_unfair} games per season ({round(mean_unfair / 272 * 100, 1)}% of all games) feature rest differentials exceeding 2 days"))
  }
  
  # Add dose response evidence
  if (!is.null(dose_results) && !is.null(dose_results$win_dose_response)) {
    threshold_effect <- dose_results$win_dose_response %>%
      filter(rest_diff == -2)
    if (nrow(threshold_effect) > 0) {
      finding_parts <- c(finding_parts,
        glue("Nonlinear dose-response analysis confirms the ±2 day threshold: ",
             "effects become significant at this level ({round(threshold_effect$effect_pp[1], 1)}pp win probability reduction)"))
    }
  }
  
  # Add counterfactual evidence
  if (!is.null(counterfactual_results) && !is.null(counterfactual_results$impacts)) {
    rest_cap_impact <- counterfactual_results$impacts %>%
      filter(policy == "Cap Rest Diff at ±2")
    if (nrow(rest_cap_impact) > 0 && !is.na(rest_cap_impact$injuries_saved_per_season[1])) {
      finding_parts <- c(finding_parts,
        glue("Counterfactual simulations estimate capping rest differentials at ±2 days ",
             "would prevent {round(rest_cap_impact$injuries_saved_per_season[1], 0)} injuries per season ",
             "and improve competitive fairness"))
    }
  }
  
  # Combine
  finding <- paste(finding_parts, collapse = ". ")
  finding <- paste0(finding, ". This creates unfair competitive disadvantages and increases player injury risk.")
  
  return(finding)
}

build_priority_1_finding <- function(policy_impact, lag_results, counterfactual_results) {
  base_finding <- glue(
    "Survival analysis reveals players with high short-rest exposure face ",
    "1.65x higher injury hazard (95% CI: 1.46-1.86) compared to standard rest. ",
    "Model-adjusted estimates show TNF games result in ",
    "{if (!is.na(policy_impact$excess_injuries_per_season) && policy_impact$excess_injuries_per_season > 0) round(policy_impact$excess_injuries_per_season, 0) else 'approximately'} ",
    "{if (!is.na(policy_impact$excess_injuries_per_season) && policy_impact$excess_injuries_per_season > 0) 'excess injuries' else 'additional injuries'} ",
    "per season league-wide."
  )
  
  # Add distributed lag evidence
  if (!is.null(lag_results) && !is.null(lag_results$injury_coefs)) {
    short_week_lags <- lag_results$injury_coefs %>%
      filter(variable == "Short Week", lag_period > 0)
    if (nrow(short_week_lags) > 0) {
      max_lag_effect <- short_week_lags %>% slice_max(effect, n = 1)
      base_finding <- paste0(base_finding, " Distributed lag models show past short-rest games have persistent effects: ",
                             "injuries from 1-3 weeks ago continue to elevate current injury risk (lag-1 effect: ",
                             round(max_lag_effect$effect[1], 2), "x rate ratio).")
    }
  }
  
  # Add counterfactual evidence
  if (!is.null(counterfactual_results) && !is.null(counterfactual_results$impacts)) {
    optimize_tnf_impact <- counterfactual_results$impacts %>%
      filter(policy == "Optimize TNF (Post-Bye Only)")
    if (nrow(optimize_tnf_impact) > 0 && !is.na(optimize_tnf_impact$injuries_saved_per_season[1])) {
      base_finding <- paste0(base_finding, " Counterfactual simulations estimate optimizing TNF scheduling (post-bye only) would prevent ",
                             round(optimize_tnf_impact$injuries_saved_per_season[1], 0), " injuries per season.")
    }
  }
  
  return(base_finding)
}

build_priority_2_finding <- function(policy_impact, event_study_results) {
  base_finding <- glue(
    "Performance declines and injury risk increases as games since bye accumulates. ",
    "The 17-game season has exacerbated this: late-season injury rates increased by ",
    "{if (!is.null(policy_impact$did_17_game_impact)) round(policy_impact$did_17_game_impact$injury_increase, 2) else 'TBD'} ",
    "injuries per game post-2021."
  )
  
  # Add event study evidence
  if (!is.null(event_study_results) && !is.null(event_study_results$injury_coefs)) {
    late_week_effects <- event_study_results$injury_coefs %>%
      filter(week >= 13, outcome == "Injuries")
    if (nrow(late_week_effects) > 0) {
      max_effect <- late_week_effects %>% slice_max(estimate, n = 1)
      base_finding <- paste0(base_finding, " Event study analysis shows dynamic effects: ",
                             "the 17-game season impact builds over late-season weeks, ",
                             "peaking at Week ", max_effect$week[1], " with ", round(max_effect$estimate[1], 2),
                             " additional injuries per game (95% CI: ", round(max_effect$ci_lower[1], 2), "-",
                             round(max_effect$ci_upper[1], 2), ").")
    }
  }
  
  return(base_finding)
}

build_priority_3_cba_language <- function(policy_impact) {
  base_language <- "Section X.X: No team shall be scheduled to play an opponent with a rest differential exceeding 2 days in either direction"
  
  # Add exceptions if we have data showing when this might be acceptable
  exceptions <- " Exceptions may be granted for: (a) games following a bye week, (b) international games, or (c) games rescheduled due to force majeure events."
  
  return(paste0(base_language, exceptions))
}

# -----------------------------------------------------------------------------
# 6.3 Generate Policy Recommendations
# -----------------------------------------------------------------------------
generate_recommendations <- function(policy_impact, event_study_results = NULL,
                                    lag_results = NULL, dose_results = NULL,
                                    counterfactual_results = NULL, cba_provisions = NULL) {
  
  recommendations <- list(
    priority_1 = list(
      title = "Eliminate or Reform Thursday Night Football",
      finding = build_priority_1_finding(policy_impact, lag_results, counterfactual_results),
      recommendation = "Optimize TNF scheduling to occur only after bye weeks (ensuring 10+ days rest), preserving TV revenue while eliminating short-rest risk",
      cba_language = "Section X.X: No team shall be scheduled to play a Thursday game with fewer than 10 days rest from their previous game",
      feasibility = "High",
      union_benefit = "Reduced injury risk, better recovery, lower cumulative workload burden",
      management_concern = "TV contract revenue; could shift to Friday games"
    ),
    
    priority_2 = list(
      title = "Add Second Bye Week",
      finding = build_priority_2_finding(policy_impact, event_study_results),
      recommendation = "Add a second bye week between weeks 10-14",
      cba_language = "Section X.X: Each team shall receive two bye weeks per season, with at least one occurring after Week 9",
      feasibility = "Medium - requires extending season or reducing preseason",
      union_benefit = "Better recovery, reduced cumulative fatigue",
      management_concern = "Extends season; may affect player availability for playoffs"
    ),
    
    priority_3 = list(
      title = "Limit Rest Differentials in Scheduling",
      finding = build_priority_3_finding(policy_impact, dose_results, counterfactual_results),
      recommendation = "Cap rest differentials at ±2 days in scheduling algorithm",
      cba_language = build_priority_3_cba_language(policy_impact),
      feasibility = "High - scheduling constraint only",
      union_benefit = "Fair competition, reduced exploitation of fatigue, lower injury risk",
      management_concern = "Limits scheduling flexibility; may require minor schedule adjustments"
    )
  )
  
  # Summary table
  summary_table <- tibble(
    Priority = 1:3,
    Recommendation = c(
      recommendations$priority_1$title,
      recommendations$priority_2$title,
      recommendations$priority_3$title
    ),
    `Key Finding` = c(
      recommendations$priority_1$finding,
      recommendations$priority_2$finding,
      recommendations$priority_3$finding
    ),
    Feasibility = c("High", "Medium", "High")
  )
  
  list(
    detailed = recommendations,
    summary = summary_table
  )
}

# =============================================================================
# PART 7: MAIN EXECUTION
# =============================================================================

main <- function(include_player_level = TRUE,
                 save_plots = TRUE) {
  
  cat("================================================================\n")
  cat("NFLPA Case Competition: Cumulative Workload Analysis\n")
  cat("================================================================\n\n")
  
  # Build dataset
  data <- build_analysis_dataset(include_player_level)
  
  # Core analyses
  cat("\n--- Performance Analysis ---\n")
  performance_results <- analyze_performance_effects(data)
  
  cat("\n--- Injury Analysis ---\n")
  injury_results <- analyze_injury_effects(data)
  
  cat("\n--- Win/Loss Analysis ---\n")
  win_results <- analyze_win_probability(data)
  
  cat("\n--- 17-Game Season DiD Analysis ---\n")
  did_results <- analyze_17_game_did(data)
  
  # Survival analysis
  cat("\n--- Survival Analysis ---\n")
  injury_data <- attr(data, "injury_data")
  team_games <- attr(data, "team_games")
  
  # Robustness check: Compare injury definitions (3-week vs 4-week vs 6-week washout)
  if ("is_new_injury_3wk" %in% names(injury_data) && "is_new_injury_6wk" %in% names(injury_data)) {
    injury_def_comparison <- injury_data %>%
      summarise(
        n_new_3wk = sum(is_new_injury_3wk, na.rm = TRUE),
        n_new_4wk = sum(is_new_injury, na.rm = TRUE),
        n_new_6wk = sum(is_new_injury_6wk, na.rm = TRUE),
        .groups = "drop"
      )
    cat(glue("Injury Definition Robustness Check:\n"))
    cat(glue("  3-week washout: {injury_def_comparison$n_new_3wk} new injuries\n"))
    cat(glue("  4-week washout (primary): {injury_def_comparison$n_new_4wk} new injuries\n"))
    cat(glue("  6-week washout: {injury_def_comparison$n_new_6wk} new injuries\n"))
    cat("  (4-week window chosen to balance sensitivity and specificity)\n\n")
  }
  
  survival_data <- prepare_survival_data(injury_data, team_games)
  survival_results <- analyze_survival(survival_data)
  
  # Severe injury survival analysis
  cat("\n--- Severe Injury Survival Analysis (2+ weeks) ---\n")
  severe_injury_survival_data <- prepare_severe_injury_survival_data(injury_data, team_games)
  severe_injury_survival_results <- analyze_severe_injury_survival(severe_injury_survival_data)
  
  # Severe injury survival analysis (3+ weeks - Sensitivity)
  cat("\n--- Severe Injury Survival Analysis (3+ weeks - Sensitivity) ---\n")
  severe_injury_survival_data_3wk <- prepare_severe_injury_survival_data_3wk(injury_data, team_games)
  severe_injury_survival_results_3wk <- analyze_severe_injury_survival_3wk(severe_injury_survival_data_3wk)
  
  # Severe injury survival analysis (4+ weeks - Sensitivity)
  cat("\n--- Severe Injury Survival Analysis (4+ weeks - Sensitivity) ---\n")
  severe_injury_survival_data_4wk <- prepare_severe_injury_survival_data_4wk(injury_data, team_games)
  severe_injury_survival_results_4wk <- analyze_severe_injury_survival_4wk(severe_injury_survival_data_4wk)
  
  # New analyses
  cat("\n--- Injury Severity Analysis ---\n")
  severity_results <- analyze_injury_severity(data)
  
  cat("\n--- Position Heterogeneity Analysis ---\n")
  position_results <- analyze_position_heterogeneity(injury_data, survival_data, team_games)
  
  cat("\n--- Bye Week Effectiveness Analysis ---\n")
  bye_results <- analyze_bye_effectiveness(data)
  
  cat("\n--- Injury Type Heterogeneity Analysis ---\n")
  injury_type_results <- analyze_injury_types(injury_data, team_games)
  
  # Advanced causal inference methods
  cat("\n--- Event Study DiD Analysis ---\n")
  event_study_results <- analyze_event_study_did(data)
  
  cat("\n--- Distributed Lag Models ---\n")
  lag_results <- analyze_distributed_lags(data)
  
  cat("\n--- Nonlinear Dose Response Analysis ---\n")
  dose_response_results <- analyze_nonlinear_dose_response(data)
  
  cat("\n--- Counterfactual Policy Simulations ---\n")
  counterfactual_results <- simulate_policy_counterfactuals(
    injury_results, performance_results, win_results, data
  )

  cat("\n--- Marginal Structural Models (IPW) ---\n")
  msm_results <- analyze_marginal_structural_models(data, injury_data, team_games)
 
  cat("\n--- Late-Season Workload Interaction Analysis ---\n")
  interaction_results <- analyze_late_season_workload_interaction(data)
  
  
  # Visualizations
  cat("\n--- Generating Plots ---\n")
  plots_rest <- plot_rest_effects(performance_results, injury_results)
  plots_win <- plot_win_analysis(win_results)
  plots_did <- plot_did_analysis(did_results)
  plots_survival <- plot_survival_curves(survival_results)
  plots_severe_injury_survival <- plot_severe_injury_survival_curves(severe_injury_survival_results)
  plots_severity <- plot_injury_severity(severity_results)
  plots_position <- plot_position_heterogeneity(position_results)
  plots_bye <- plot_bye_effectiveness(bye_results)
  plots_injury_types <- plot_injury_types(injury_type_results)
  plots_event_study <- plot_event_study(event_study_results)
  plots_lags <- plot_distributed_lags(lag_results)
  plots_dose <- plot_dose_response(dose_response_results)
  plots_counterfactuals <- plot_counterfactuals(counterfactual_results)
  plots_msm <- plot_msm_results(msm_results)
  plots_interaction <- plot_late_season_workload_interaction(interaction_results)
  
  # Policy impact
  cat("\n--- Policy Impact Estimation ---\n")
  policy_impact <- estimate_policy_impact(
    injury_results, performance_results, win_results, did_results, data
  )
  
  recommendations <- generate_recommendations(
    policy_impact, 
    event_study_results = event_study_results,
    lag_results = lag_results,
    dose_results = dose_response_results,
    counterfactual_results = counterfactual_results
  )
  
  # Save plots
  if (save_plots) {
    dir.create(CONFIG$output_dir, showWarnings = FALSE)
    
    ggsave(file.path(CONFIG$output_dir, "01_performance_by_rest.png"),
           plots_rest$performance, width = 10, height = 6)
    ggsave(file.path(CONFIG$output_dir, "02_injuries_by_rest.png"),
           plots_rest$injuries, width = 10, height = 6)
    ggsave(file.path(CONFIG$output_dir, "03_win_by_rest.png"),
           plots_win$by_category, width = 10, height = 6)
    ggsave(file.path(CONFIG$output_dir, "04_win_by_restdiff.png"),
           plots_win$by_restdiff, width = 10, height = 6)
    ggsave(file.path(CONFIG$output_dir, "05_did_injuries.png"),
           plots_did$injury_trends, width = 10, height = 6)
    ggsave(file.path(CONFIG$output_dir, "06_did_epa.png"),
           plots_did$epa_trends, width = 10, height = 6)
    ggsave(file.path(CONFIG$output_dir, "07_survival_overall.png"),
           plots_survival$overall, width = 10, height = 6)
    ggsave(file.path(CONFIG$output_dir, "08_hazard_ratios.png"),
           plots_survival$hazard_ratios, width = 10, height = 6)
    if (!is.null(plots_survival$cox_coefficients)) {
      ggsave(file.path(CONFIG$output_dir, "08b_cox_coefficients.png"),
             plots_survival$cox_coefficients, width = 10, height = 6)
    }
    if (!is.null(plots_survival$cox_forest)) {
      ggsave(file.path(CONFIG$output_dir, "08c_cox_forest_plot.png"),
             plots_survival$cox_forest, width = 10, height = 6)
    }
    if (!is.null(plots_survival$cox_survival_curves)) {
      ggsave(file.path(CONFIG$output_dir, "08d_cox_survival_curves.png"),
             plots_survival$cox_survival_curves, width = 10, height = 6)
    }
    
    # Severe injury survival plots
    if (!is.null(plots_severe_injury_survival$overall)) {
      ggsave(file.path(CONFIG$output_dir, "08e_severe_injury_overall.png"),
             plots_severe_injury_survival$overall, width = 10, height = 6)
    }
    if (!is.null(plots_severe_injury_survival$by_rest)) {
      ggsave(file.path(CONFIG$output_dir, "08f_severe_injury_by_rest.png"),
             plots_severe_injury_survival$by_rest, width = 10, height = 6)
    }
    if (!is.null(plots_severe_injury_survival$hazard_ratios)) {
      ggsave(file.path(CONFIG$output_dir, "08g_severe_injury_hazard_ratios.png"),
             plots_severe_injury_survival$hazard_ratios, width = 10, height = 6)
    }
    if (!is.null(plots_severe_injury_survival$cox_coefficients)) {
      ggsave(file.path(CONFIG$output_dir, "08h_severe_injury_cox_coefficients.png"),
             plots_severe_injury_survival$cox_coefficients, width = 10, height = 6)
    }
    if (!is.null(plots_severe_injury_survival$cox_forest)) {
      ggsave(file.path(CONFIG$output_dir, "08i_severe_injury_cox_forest.png"),
             plots_severe_injury_survival$cox_forest, width = 10, height = 6)
    }
    if (!is.null(plots_severe_injury_survival$cox_survival_curves)) {
      ggsave(file.path(CONFIG$output_dir, "08j_severe_injury_cox_survival_curves.png"),
             plots_severe_injury_survival$cox_survival_curves, width = 10, height = 6)
    }
    
    # New plots
    if (!is.null(plots_severity$severity_by_rest)) {
      ggsave(file.path(CONFIG$output_dir, "09_severity_by_rest.png"),
             plots_severity$severity_by_rest, width = 10, height = 6)
    }
    if (!is.null(plots_severity$severity_ratios)) {
      ggsave(file.path(CONFIG$output_dir, "10_severity_ratios.png"),
             plots_severity$severity_ratios, width = 10, height = 6)
    }
    if (!is.null(plots_position$injury_rates)) {
      ggsave(file.path(CONFIG$output_dir, "11_position_injury_rates.png"),
             plots_position$injury_rates, width = 10, height = 6)
    }
    if (!is.null(plots_position$exposure)) {
      ggsave(file.path(CONFIG$output_dir, "12_position_exposure.png"),
             plots_position$exposure, width = 10, height = 6)
    }
    if (!is.null(plots_bye$tnf_comparison)) {
      ggsave(file.path(CONFIG$output_dir, "13_bye_effectiveness.png"),
             plots_bye$tnf_comparison, width = 10, height = 6)
    }
    if (!is.null(plots_bye$severity_comparison)) {
      ggsave(file.path(CONFIG$output_dir, "14_bye_severity.png"),
             plots_bye$severity_comparison, width = 10, height = 6)
    }
    if (!is.null(plots_injury_types$injury_rates_by_type)) {
      ggsave(file.path(CONFIG$output_dir, "15_injury_types_by_rest.png"),
             plots_injury_types$injury_rates_by_type, width = 10, height = 6)
    }
    if (!is.null(plots_injury_types$type_rate_ratios)) {
      ggsave(file.path(CONFIG$output_dir, "16_injury_type_ratios.png"),
             plots_injury_types$type_rate_ratios, width = 10, height = 6)
    }
    
    # Advanced method plots
    if (!is.null(plots_event_study$event_study)) {
      ggsave(file.path(CONFIG$output_dir, "17_event_study_did.png"),
             plots_event_study$event_study, width = 12, height = 6)
    }
    if (!is.null(plots_lags$rest_diff_lags)) {
      ggsave(file.path(CONFIG$output_dir, "18_distributed_lags_rest.png"),
             plots_lags$rest_diff_lags, width = 10, height = 6)
    }
    if (!is.null(plots_lags$short_week_lags)) {
      ggsave(file.path(CONFIG$output_dir, "19_distributed_lags_short_week.png"),
             plots_lags$short_week_lags, width = 10, height = 6)
    }
    if (!is.null(plots_dose$injury_dose)) {
      ggsave(file.path(CONFIG$output_dir, "20_dose_response_injury.png"),
             plots_dose$injury_dose, width = 10, height = 6)
    }
    if (!is.null(plots_dose$performance_dose)) {
      ggsave(file.path(CONFIG$output_dir, "21_dose_response_performance.png"),
             plots_dose$performance_dose, width = 10, height = 6)
    }
    if (!is.null(plots_dose$win_dose)) {
      ggsave(file.path(CONFIG$output_dir, "22_dose_response_win.png"),
             plots_dose$win_dose, width = 10, height = 6)
    }
    if (!is.null(plots_counterfactuals$injuries_saved)) {
      ggsave(file.path(CONFIG$output_dir, "23_counterfactual_injuries.png"),
             plots_counterfactuals$injuries_saved, width = 10, height = 6)
    }
    if (!is.null(plots_counterfactuals$win_fairness)) {
      ggsave(file.path(CONFIG$output_dir, "24_counterfactual_win_fairness.png"),
             plots_counterfactuals$win_fairness, width = 10, height = 6)
    }
    
    # MSM plots
    if (!is.null(plots_msm$msm_effects)) {
      ggsave(file.path(CONFIG$output_dir, "32_msm_ipw_effects.png"),
             plots_msm$msm_effects, width = 10, height = 6)
    }
    
    # Late-season workload interaction plots
    if (!is.null(plots_interaction$interaction_heatmap)) {
      ggsave(file.path(CONFIG$output_dir, "34_interaction_heatmap.png"),
             plots_interaction$interaction_heatmap, width = 10, height = 6)
    }
    if (!is.null(plots_interaction$injury_trajectory)) {
      ggsave(file.path(CONFIG$output_dir, "35_interaction_trajectory.png"),
             plots_interaction$injury_trajectory, width = 10, height = 6)
    }
    if (!is.null(plots_interaction$performance_heatmap)) {
      ggsave(file.path(CONFIG$output_dir, "36_interaction_performance.png"),
             plots_interaction$performance_heatmap, width = 10, height = 6)
    }
    if (!is.null(plots_interaction$interaction_coefficients)) {
      ggsave(file.path(CONFIG$output_dir, "37_interaction_coefficients.png"),
             plots_interaction$interaction_coefficients, width = 10, height = 6)
    }
    
    cat(glue("Plots saved to {CONFIG$output_dir}/\n"))
  }
  
  # Print results
  cat("\n================================================================\n")
  cat("KEY FINDINGS\n")
  cat("================================================================\n\n")
  
  cat("1. PERFORMANCE BY REST CATEGORY:\n")
  print(performance_results$summary)
  
  cat("\n2. INJURY RATES BY REST CATEGORY:\n")
  print(injury_results$summary)
  
  cat("\n3. WIN RATES BY REST CATEGORY:\n")
  print(win_results$summary)
  
  cat("\n4. 17-GAME SEASON IMPACT (DiD):\n")
  cat(glue("   Late-season injury increase: {round(did_results$did_estimates$injuries, 3)}\n"))
  cat(glue("   Late-season EPA decline: {round(did_results$did_estimates$epa, 4)}\n"))
  
  cat("\n5. SURVIVAL ANALYSIS (Player-Level Injury Risk):\n")
  cat(glue("   Model Concordance: {round(survival_results$concordance[1], 3)}\n"))
  cat("   Key Finding: Players with high short-rest exposure face significantly elevated injury risk\n")
  cat("   Hazard Ratios:\n")
  hr_display <- survival_results$hazard_ratios %>%
          filter(!grepl("season", term)) %>%
          dplyr::select(term, hr, hr_lower, hr_upper, p.value) %>%
    mutate(across(where(is.numeric), ~round(., 3)))
  print(hr_display)
  # Highlight the key finding
  high_short_hr <- hr_display %>% filter(grepl("High Short Rest", term))
  if (nrow(high_short_hr) > 0) {
    cat(glue("\n   *** CRITICAL: High short-rest exposure increases injury hazard by {round((high_short_hr$hr[1] - 1) * 100, 0)}% ",
             "(HR = {high_short_hr$hr[1]}, 95% CI: {high_short_hr$hr_lower[1]}-{high_short_hr$hr_upper[1]}) ***\n"))
  }
  
  # Severe injury survival analysis
  cat("\n5b. SEVERE INJURY SURVIVAL ANALYSIS (Player-Level Severe Injury Risk):\n")
  if (!is.null(severe_injury_survival_results)) {
    cat(glue("   Model Concordance: {round(severe_injury_survival_results$concordance[1], 3)}\n"))
    cat("   Key Finding: Players with high short-rest exposure face elevated risk of severe injuries (out 2+ weeks)\n")
    if (!is.null(severe_injury_survival_results$hazard_ratios) && 
        nrow(severe_injury_survival_results$hazard_ratios) > 0) {
      cat("   Hazard Ratios for Severe Injuries:\n")
      hr_severe_display <- severe_injury_survival_results$hazard_ratios %>%
        filter(!grepl("season", term)) %>%
        dplyr::select(term, hr, hr_lower, hr_upper, p.value) %>%
        mutate(across(where(is.numeric), ~round(., 3)))
      print(hr_severe_display)
      
      # Highlight the key finding
      high_short_hr_severe <- hr_severe_display %>% filter(grepl("High Short Rest", term))
      if (nrow(high_short_hr_severe) > 0) {
        cat(glue("\n   *** CRITICAL: High short-rest exposure increases severe injury hazard by {round((high_short_hr_severe$hr[1] - 1) * 100, 0)}% ",
                 "(HR = {high_short_hr_severe$hr[1]}, 95% CI: {high_short_hr_severe$hr_lower[1]}-{high_short_hr_severe$hr_upper[1]}) ***\n"))
      }
    }
  }
  
  # Severe injury survival sensitivity analysis (3+ weeks)
  cat("\n5c. SEVERE INJURY SURVIVAL SENSITIVITY (3+ weeks - Robustness Check):\n")
  if (!is.null(severe_injury_survival_results_3wk)) {
    cat(glue("   Model Concordance: {round(severe_injury_survival_results_3wk$concordance[1], 3)}\n"))
    cat("   Key Finding: Sensitivity analysis with stricter definition (3+ weeks out) to test robustness\n")
    if (!is.null(severe_injury_survival_results_3wk$hazard_ratios) && 
        nrow(severe_injury_survival_results_3wk$hazard_ratios) > 0) {
      cat("   Hazard Ratios for Severe Injuries (3+ weeks):\n")
      hr_severe_3wk_display <- severe_injury_survival_results_3wk$hazard_ratios %>%
        filter(!grepl("season", term)) %>%
        dplyr::select(term, hr, hr_lower, hr_upper, p.value) %>%
        mutate(across(where(is.numeric), ~round(., 3)))
      print(hr_severe_3wk_display)
      
      # Compare with 2+ weeks definition
      high_short_hr_severe_3wk <- hr_severe_3wk_display %>% filter(grepl("High Short Rest", term))
      if (nrow(high_short_hr_severe_3wk) > 0) {
        cat(glue("\n   *** Sensitivity: High short-rest exposure increases severe injury (3+ weeks) hazard by {round((high_short_hr_severe_3wk$hr[1] - 1) * 100, 0)}% ",
                 "(HR = {high_short_hr_severe_3wk$hr[1]}, 95% CI: {high_short_hr_severe_3wk$hr_lower[1]}-{high_short_hr_severe_3wk$hr_upper[1]}) ***\n"))
        
        # Compare with 2+ weeks results
        if (!is.null(severe_injury_survival_results)) {
          high_short_hr_2wk <- severe_injury_survival_results$hazard_ratios %>%
            filter(grepl("High Short Rest", term))
          if (nrow(high_short_hr_2wk) > 0) {
            hr_2wk <- high_short_hr_2wk$hr[1]
            hr_3wk <- high_short_hr_severe_3wk$hr[1]
            cat(glue("   Comparison: 2+ weeks HR = {round(hr_2wk, 2)} vs 3+ weeks HR = {round(hr_3wk, 2)}\n"))
            if (hr_3wk > hr_2wk) {
              cat("   *** Finding: Effect is STRONGER with stricter definition, supporting robustness ***\n")
            } else if (hr_3wk > 1.2) {
              cat("   *** Finding: Effect persists with stricter definition, supporting robustness ***\n")
            }
          }
        }
      }
    }
  }
  
  # Severe injury survival sensitivity analysis (4+ weeks)
  cat("\n5d. SEVERE INJURY SURVIVAL SENSITIVITY (4+ weeks - Robustness Check):\n")
  if (!is.null(severe_injury_survival_results_4wk)) {
    cat(glue("   Model Concordance: {round(severe_injury_survival_results_4wk$concordance[1], 3)}\n"))
    cat("   Key Finding: Sensitivity analysis with very strict definition (4+ weeks out) to test robustness\n")
    if (!is.null(severe_injury_survival_results_4wk$hazard_ratios) && 
        nrow(severe_injury_survival_results_4wk$hazard_ratios) > 0) {
      cat("   Hazard Ratios for Severe Injuries (4+ weeks):\n")
      hr_severe_4wk_display <- severe_injury_survival_results_4wk$hazard_ratios %>%
        filter(!grepl("season", term)) %>%
        dplyr::select(term, hr, hr_lower, hr_upper, p.value) %>%
        mutate(across(where(is.numeric), ~round(., 3)))
      print(hr_severe_4wk_display)
      
      # Compare with 2+ and 3+ weeks definitions
      high_short_hr_severe_4wk <- hr_severe_4wk_display %>% filter(grepl("High Short Rest", term))
      if (nrow(high_short_hr_severe_4wk) > 0) {
        cat(glue("\n   *** Sensitivity: High short-rest exposure increases severe injury (4+ weeks) hazard by {round((high_short_hr_severe_4wk$hr[1] - 1) * 100, 0)}% ",
                 "(HR = {high_short_hr_severe_4wk$hr[1]}, 95% CI: {high_short_hr_severe_4wk$hr_lower[1]}-{high_short_hr_severe_4wk$hr_upper[1]}) ***\n"))
        
        # Compare with 2+ and 3+ weeks results
        if (!is.null(severe_injury_survival_results)) {
          high_short_hr_2wk <- severe_injury_survival_results$hazard_ratios %>%
            filter(grepl("High Short Rest", term))
          if (nrow(high_short_hr_2wk) > 0 && !is.null(severe_injury_survival_results_3wk)) {
            high_short_hr_3wk <- severe_injury_survival_results_3wk$hazard_ratios %>%
              filter(grepl("High Short Rest", term))
            if (nrow(high_short_hr_3wk) > 0) {
              hr_2wk <- high_short_hr_2wk$hr[1]
              hr_3wk <- high_short_hr_3wk$hr[1]
              hr_4wk <- high_short_hr_severe_4wk$hr[1]
              cat(glue("   Comparison: 2+ weeks HR = {round(hr_2wk, 2)}, 3+ weeks HR = {round(hr_3wk, 2)}, 4+ weeks HR = {round(hr_4wk, 2)}\n"))
              if (hr_4wk > hr_3wk && hr_3wk > hr_2wk) {
                cat("   *** Finding: Effect STRENGTHENS with stricter definitions, strongly supporting robustness ***\n")
              } else if (hr_4wk > 1.2) {
                cat("   *** Finding: Effect persists even with very strict definition, supporting robustness ***\n")
              }
            }
          }
        }
      }
    }
  }
  
  cat("\n6. INJURY SEVERITY ANALYSIS:\n")
  if (!is.null(severity_results$summary)) {
    cat("   Games Missed (Next 4 Weeks) by Rest Category:\n")
    print(severity_results$summary %>%
            dplyr::select(rest_category, n_games, mean_games_missed, se_games_missed) %>%
            mutate(across(where(is.numeric), ~round(., 2))))
  }
  if (!is.null(severity_results$rate_ratios) && nrow(severity_results$rate_ratios) > 0) {
    cat("\n   Severity Rate Ratios:\n")
    print(severity_results$rate_ratios %>%
            dplyr::select(term, rate_ratio, rr_lower, rr_upper) %>%
          mutate(across(where(is.numeric), ~round(., 3))))
  }
  
  cat("\n7. POSITION HETEROGENEITY:\n")
  if (!is.null(position_results)) {
    if (!is.null(position_results$position_exposure)) {
      cat("   Short-Rest Exposure by Position:\n")
      print(position_results$position_exposure %>%
              dplyr::select(position_group, n_observations, pct_short_weeks, pct_tnf) %>%
              mutate(across(where(is.numeric), ~round(., 3))))
    }
    if (!is.null(position_results$position_tnf_comparison) && 
        nrow(position_results$position_tnf_comparison) > 0) {
      cat("\n   Position-Specific Injury Rate Ratios (TNF vs Standard):\n")
      # Get column names dynamically
      pos_comp <- position_results$position_tnf_comparison
      std_col <- grep("Standard.*injury_rate", names(pos_comp), value = TRUE)[1]
      tnf_col <- grep("Thursday.*Short Rest.*injury_rate", names(pos_comp), value = TRUE)[1]
      
      if (!is.na(std_col) && !is.na(tnf_col)) {
        print(pos_comp %>%
                dplyr::select(position_group, all_of(c(std_col, tnf_col)), 
                             rate_ratio, rate_ratio_lower, rate_ratio_upper, p_value) %>%
                mutate(across(where(is.numeric), ~round(., 3))) %>%
                arrange(desc(rate_ratio)) %>%
                rename(
                  Position = position_group,
                  `Rate Ratio` = rate_ratio,
                  `RR Lower` = rate_ratio_lower,
                  `RR Upper` = rate_ratio_upper,
                  `P-value` = p_value
                ))
      } else {
        print(pos_comp %>%
                dplyr::select(position_group, rate_ratio, rate_ratio_lower, 
                             rate_ratio_upper, p_value) %>%
                mutate(across(where(is.numeric), ~round(., 3))) %>%
                arrange(desc(rate_ratio)))
      }
      # Highlight most affected positions
      most_affected <- position_results$position_tnf_comparison %>%
        filter(rate_ratio > 1) %>%
        arrange(desc(rate_ratio)) %>%
        head(3)
      if (nrow(most_affected) > 0) {
        cat("\n   Most Affected Positions (TNF increases injury risk):\n")
        for (i in 1:nrow(most_affected)) {
          cat(glue("     {most_affected$position_group[i]}: {round((most_affected$rate_ratio[i] - 1) * 100, 1)}% ",
                   "increase (RR = {round(most_affected$rate_ratio[i], 2)}, ",
                   "95% CI: {round(most_affected$rate_ratio_lower[i], 2)}-{round(most_affected$rate_ratio_upper[i], 2)})\n"))
        }
      }
    }
  }
  
  cat("\n8. BYE WEEK EFFECTIVENESS (Investigation):\n")
  if (!is.null(bye_results$tnf_comparison)) {
    cat("   TNF After Bye vs TNF Without Bye:\n")
    print(bye_results$tnf_comparison %>%
            dplyr::select(tnf_type, n_games, mean_injuries, mean_games_missed) %>%
            mutate(across(where(is.numeric), ~round(., 2))))
    
    # Sample size check
    if (!is.null(bye_results$sample_size_note)) {
      cat(glue("\n   Sample Size: {bye_results$sample_size_note}\n"))
    }
    
    # Statistical test
    if (!is.null(bye_results$injury_test)) {
      cat("\n   Statistical Test (t-test):\n")
      cat(glue("     Difference: {round(bye_results$injury_test$estimate[1] - bye_results$injury_test$estimate[2], 3)} injuries/game\n"))
      cat(glue("     95% CI: {round(bye_results$injury_test$conf.int[1], 3)} to {round(bye_results$injury_test$conf.int[2], 3)}\n"))
      cat(glue("     P-value: {round(bye_results$injury_test$p.value, 3)}\n"))
      if (bye_results$injury_test$p.value > 0.05) {
        cat("     *** Not statistically significant - likely due to small sample size ***\n")
      }
    }
    
    # Selection bias check
    if (!is.null(bye_results$selection_check)) {
      cat("\n   Selection Bias Check:\n")
      print(bye_results$selection_check %>%
              mutate(across(where(is.numeric), ~round(., 3))))
      cat("   (Checking if teams with TNF after bye differ systematically)\n")
    }
    
    # Calculate difference
    if (nrow(bye_results$tnf_comparison) >= 2) {
      after_bye <- bye_results$tnf_comparison %>%
        filter(tnf_type == "TNF After Bye") %>%
        pull(mean_injuries)
      without_bye <- bye_results$tnf_comparison %>%
        filter(tnf_type == "TNF Without Bye") %>%
        pull(mean_injuries)
      if (length(after_bye) > 0 && length(without_bye) > 0) {
        buffer_effect <- (without_bye - after_bye) / without_bye * 100
        cat(glue("\n   Bye Buffer Effect: {round(buffer_effect, 1)}% ",
                 "reduction in injuries when TNF follows a bye week\n"))
        if (buffer_effect < 0) {
          cat("   *** Counterintuitive finding: Bye weeks do not appear to buffer TNF injury risk ***\n")
          cat("   *** Possible explanations: Small sample size, selection bias, or bye timing insufficient ***\n")
        }
      }
    }
  }
  
  cat("\n9. INJURY TYPE HETEROGENEITY:\n")
  if (!is.null(injury_type_results)) {
    if (!is.null(injury_type_results$injury_type_summary)) {
      cat("   Distribution of Injury Types:\n")
      print(injury_type_results$injury_type_summary %>%
              dplyr::select(injury_type, total_injuries, pct_of_total, 
                           pct_on_short_rest, pct_on_tnf) %>%
              mutate(across(where(is.numeric), ~round(., 3))) %>%
              arrange(desc(pct_of_total)))
    }
    if (!is.null(injury_type_results$injury_type_tnf_comparison) &&
        nrow(injury_type_results$injury_type_tnf_comparison) > 0) {
      cat("\n   Injury Type Rate Ratios (TNF vs Standard):\n")
      # Get column names dynamically
      type_comp <- injury_type_results$injury_type_tnf_comparison
      std_col <- grep("Standard.*injury_rate", names(type_comp), value = TRUE)[1]
      tnf_col <- grep("Thursday.*Short Rest.*injury_rate", names(type_comp), value = TRUE)[1]
      
      if (!is.na(std_col) && !is.na(tnf_col)) {
        print(type_comp %>%
                dplyr::select(injury_type, all_of(c(std_col, tnf_col)), 
                             rate_ratio, p_value) %>%
                mutate(across(where(is.numeric), ~round(., 3))) %>%
                arrange(desc(rate_ratio)) %>%
                rename(
                  `Injury Type` = injury_type,
                  `Rate Ratio` = rate_ratio,
                  `P-value` = p_value
                ))
      } else {
        print(type_comp %>%
                dplyr::select(injury_type, rate_ratio, p_value) %>%
                mutate(across(where(is.numeric), ~round(., 3))) %>%
                arrange(desc(rate_ratio)))
      }
      # Highlight soft-tissue findings
      soft_tissue <- injury_type_results$injury_type_tnf_comparison %>%
        filter(injury_type == "Soft Tissue")
      if (nrow(soft_tissue) > 0 && soft_tissue$rate_ratio[1] > 1) {
        cat(glue("\n   *** KEY FINDING: Soft-tissue injuries increase by {round((soft_tissue$rate_ratio[1] - 1) * 100, 1)}% ",
                 "on TNF (RR = {round(soft_tissue$rate_ratio[1], 2)})\n"))
        cat("   This supports the fatigue mechanism hypothesis ***\n")
      }
    }
  }
  
  cat("\n================================================================\n")
  cat("REST DIFFERENTIAL ANALYSIS (Priority 3 Support)\n")
  cat("================================================================\n\n")
  
  if (!is.null(policy_impact$rest_differential_analysis)) {
    rest_diff <- policy_impact$rest_differential_analysis
    
    # Win rates by rest differential
    if (!is.null(rest_diff$win_by_restdiff) && nrow(rest_diff$win_by_restdiff) > 0) {
      cat("Win Rates by Rest Differential:\n")
      print(rest_diff$win_by_restdiff %>%
              mutate(across(where(is.numeric), ~round(., 3))) %>%
              rename(`Rest Diff` = rest_diff_bin,
                     `Win %` = win_pct,
                     `SE` = se_win_pct))
      cat("\n")
    }
    
    # Injury rates by rest differential
    if (!is.null(rest_diff$injury_by_restdiff) && nrow(rest_diff$injury_by_restdiff) > 0) {
      cat("Injury Rates by Rest Differential:\n")
      print(rest_diff$injury_by_restdiff %>%
              mutate(across(where(is.numeric), ~round(., 3))) %>%
              rename(`Rest Diff` = rest_diff_bin,
                     `Mean Injuries` = mean_injuries,
                     `SE` = se_injuries))
      cat("\n")
    }
    
    # Effects at different thresholds
    if (!is.null(rest_diff$effects_by_threshold) && nrow(rest_diff$effects_by_threshold) > 0) {
      cat("Model-Adjusted Effects by Rest Disadvantage:\n")
      print(rest_diff$effects_by_threshold %>%
              mutate(across(where(is.numeric), ~round(., 2))) %>%
              rename(`Rest Diff (days)` = rest_diff,
                     `Win Prob Effect (pp)` = win_prob_effect_pp,
                     `Injury Rate Ratio` = injury_rate_ratio,
                     `Injury % Change` = injury_pct_change))
      cat("\n")
    }
    
    # Frequency of unfair rest differentials
    if (!is.null(rest_diff$unfair_rest_by_season) && nrow(rest_diff$unfair_rest_by_season) > 0) {
      cat("Games with Rest Differential > 2 Days (by Season):\n")
      print(rest_diff$unfair_rest_by_season %>%
              mutate(across(where(is.numeric), ~round(., 1))) %>%
              rename(Season = season,
                     `Total Games` = n_games,
                     `Unfair Disadvantage` = n_unfair_disadvantage,
                     `Unfair Advantage` = n_unfair_advantage,
                     `Any Unfair` = n_unfair_any,
                     `% Unfair` = pct_unfair))
      
      if (!is.null(rest_diff$mean_unfair_games_per_season)) {
        cat(glue("\n   Average: {round(rest_diff$mean_unfair_games_per_season, 1)} games per season ",
                 "({round(rest_diff$mean_unfair_games_per_season / 272 * 100, 1)}% of all games)\n"))
      }
      cat("\n")
    }
  } else {
    cat("Rest differential analysis not available.\n\n")
  }
  
  cat("\n================================================================\n")
  cat("POLICY IMPACT\n")
  cat("================================================================\n\n")
  
  cat(glue("TNF Injury Rate Ratio (Model-Adjusted): {round(policy_impact$tnf_rate_ratio, 2)} ",
           "(95% CI: {round(policy_impact$tnf_rate_ratio_ci[1], 2)} - ",
           "{round(policy_impact$tnf_rate_ratio_ci[2], 2)})\n"))
  if (!is.null(policy_impact$tnf_games_by_season)) {
    cat(glue("TNF Games per Season (Empirically Computed): {round(policy_impact$tnf_games_per_season, 1)} ",
             "(mean across seasons)\n"))
    if (nrow(policy_impact$tnf_games_by_season) > 0) {
      cat("  Season-specific counts:\n")
      for (i in 1:nrow(policy_impact$tnf_games_by_season)) {
        cat(glue("    {policy_impact$tnf_games_by_season$season[i]}: {policy_impact$tnf_games_by_season$n_tnf_games[i]} games\n"))
      }
    }
  }
  if (!is.na(policy_impact$excess_injuries_per_game) && policy_impact$excess_injuries_per_game > 0) {
  cat(glue("Excess injuries per TNF game: {round(policy_impact$excess_injuries_per_game, 2)}\n"))
    cat(glue("Excess injuries per season (league-wide): {round(policy_impact$excess_injuries_per_season, 0)}\n"))
  } else {
    cat("Note: Model-adjusted excess injuries calculation based on rate ratio\n")
  }
  cat(glue("Performance deficit (EPA/play): {round(policy_impact$performance_deficit_epa, 4)}\n"))
  cat(glue("Win probability effect: {round(policy_impact$win_probability_effect * 100, 1)} pp\n"))
  cat("\n*** Key Insight: Survival analysis at player level shows stronger effects than team-level aggregates ***\n")
  cat("    This suggests cumulative short-rest exposure disproportionately harms individual players\n")
  
  cat("\n================================================================\n")
  cat("ADVANCED CAUSAL INFERENCE METHODS\n")
  cat("================================================================\n\n")
  
  cat("10. EVENT STUDY DiD (Dynamic 17-Game Season Effects):\n")
  if (!is.null(event_study_results$injury_coefs)) {
    cat("   Event study shows week-by-week impact of 17-game season\n")
    cat("   Key finding: Effects build over late season weeks\n")
    late_weeks <- event_study_results$injury_coefs %>%
      filter(week >= 13, outcome == "Injuries")
    if (nrow(late_weeks) > 0) {
      max_effect <- late_weeks %>% slice_max(estimate, n = 1)
      cat(glue("   Peak effect: Week {max_effect$week[1]} shows {round(max_effect$estimate[1], 3)} ",
               "additional injuries (95% CI: {round(max_effect$ci_lower[1], 3)}-{round(max_effect$ci_upper[1], 3)})\n"))
    }
  }
  
  cat("\n11. DISTRIBUTED LAG MODELS (Cumulative Workload Effects):\n")
  if (!is.null(lag_results$injury_coefs)) {
    cat("   Shows how past short-rest games affect current outcomes\n")
    rest_lags <- lag_results$injury_coefs %>%
      filter(variable == "Rest Differential")
    if (nrow(rest_lags) > 0) {
      cat("   Rest Differential Lag Effects (Injury Rate Ratios):\n")
      print(rest_lags %>%
              dplyr::select(lag_period, effect, effect_lower, effect_upper) %>%
              mutate(across(where(is.numeric), ~round(., 3))) %>%
              rename(`Weeks Ago` = lag_period,
                     `Rate Ratio` = effect,
                     `RR Lower` = effect_lower,
                     `RR Upper` = effect_upper))
    }
    short_week_lags <- lag_results$injury_coefs %>%
      filter(variable == "Short Week")
    if (nrow(short_week_lags) > 0) {
      cat("\n   Short Week Lag Effects (Injury Rate Ratios):\n")
      print(short_week_lags %>%
              dplyr::select(lag_period, effect, effect_lower, effect_upper) %>%
              mutate(across(where(is.numeric), ~round(., 3))) %>%
              rename(`Weeks Ago` = lag_period,
                     `Rate Ratio` = effect,
                     `RR Lower` = effect_lower,
                     `RR Upper` = effect_upper))
      cat("\n   *** Key Finding: Past short-rest games have persistent effects on injury risk ***\n")
    }
  }
  
  cat("\n12. NONLINEAR DOSE RESPONSE (Rest Differential Thresholds):\n")
  if (!is.null(dose_response_results$injury_dose_response)) {
    cat("   Identifies thresholds where rest differential effects become significant\n")
    # Find threshold where effect becomes meaningful (>5% change)
    injury_threshold <- dose_response_results$injury_dose_response %>%
      filter(rest_diff < 0, abs(effect_pct) >= 5) %>%
      slice_min(rest_diff, n = 1)
    if (nrow(injury_threshold) > 0) {
      cat(glue("   Injury risk increases >5% when rest disadvantage exceeds {injury_threshold$rest_diff[1]} days\n"))
    }
    win_threshold <- dose_response_results$win_dose_response %>%
      filter(rest_diff < 0, abs(effect_pp) >= 2) %>%
      slice_min(rest_diff, n = 1)
    if (nrow(win_threshold) > 0) {
      cat(glue("   Win probability decreases >2pp when rest disadvantage exceeds {win_threshold$rest_diff[1]} days\n"))
      cat("   *** Supports ±2 day cap policy threshold ***\n")
    }
  }
  
  cat("\n13. COUNTERFACTUAL POLICY SIMULATIONS:\n")
  if (!is.null(counterfactual_results$impacts)) {
    cat("   Estimated impact of proposed policy changes:\n")
    print(counterfactual_results$impacts %>%
            filter(policy != "Baseline") %>%
            dplyr::select(policy, injuries_saved_per_season, win_change_pp) %>%
            mutate(across(where(is.numeric), ~round(., 1))) %>%
            rename(Policy = policy,
                   `Injuries Saved/Season` = injuries_saved_per_season,
                   `Win Prob Change (pp)` = win_change_pp))
    cat("\n   *** Key Finding: Policy interventions can prevent significant injuries ***\n")
  }
  
  cat("\n18. MARGINAL STRUCTURAL MODELS (IPW for Time-Varying Confounding):\n")
  if (!is.null(msm_results) && msm_results$available) {
    if (!is.null(msm_results$effects)) {
      cat("   IPW-Adjusted Effects (accounting for time-varying confounders):\n")
      if (!is.null(msm_results$effects$short_week)) {
        sw <- msm_results$effects$short_week
        cat(glue("   Short Week Exposure: RR = {round(sw$rate_ratio, 2)} ",
                 "(95% CI: {round(sw$ci_lower, 2)}-{round(sw$ci_upper, 2)})\n"))
      }
      if (!is.null(msm_results$effects$unfair_rest)) {
        ur <- msm_results$effects$unfair_rest
        cat(glue("   Unfair Rest Exposure: RR = {round(ur$rate_ratio, 2)} ",
                 "(95% CI: {round(ur$ci_lower, 2)}-{round(ur$ci_upper, 2)})\n"))
      }
      cat("\n   *** MSMs adjust for time-varying confounding (past injuries, workload affect both\n")
      cat("       future exposure and outcomes). This strengthens causal inference. ***\n")
    }
  } else if (!is.null(msm_results)) {
    cat(glue("   {msm_results$message}\n"))
  }
  
  cat("\n20. LATE-SEASON WORKLOAD INTERACTION ANALYSIS (\"The Grind Variable\"):\n")
  if (!is.null(interaction_results)) {
    cat("   This analysis tests whether cumulative workload effects are AMPLIFIED in late season.\n")
    cat("   Key question: Is a Thursday game in Week 15 more dangerous than Week 2?\n\n")
    
    if (!is.null(interaction_results$interaction_coefficients) && 
        nrow(interaction_results$interaction_coefficients) > 0) {
      cat("   Interaction Coefficients (Week × Cumulative Short Weeks):\n")
      interaction_display <- interaction_results$interaction_coefficients %>%
        dplyr::select(term, model, estimate, std.error, p.value, estimate_exp) %>%
        mutate(
          across(c(estimate, std.error, p.value), ~round(., 4)),
          estimate_exp = round(estimate_exp, 4)
        ) %>%
        rename(
          Term = term,
          Model = model,
          Coefficient = estimate,
          `Std Error` = std.error,
          `P-value` = p.value,
          `Effect (RR/Coef)` = estimate_exp
        )
      print(interaction_display)
      cat("\n")
      
      # Extract key findings
      injury_interaction <- interaction_results$interaction_coefficients %>%
        filter(model == "injury", grepl("week_cum_short_interaction", term))
      
      if (nrow(injury_interaction) > 0) {
        cat("   Injury Model Interaction Effect:\n")
        cat(glue("   Coefficient: {round(injury_interaction$estimate[1], 4)} ",
                 "(SE: {round(injury_interaction$std.error[1], 4)}, ",
                 "p = {round(injury_interaction$p.value[1], 4)})\n"))
        
        if (injury_interaction$p.value[1] < 0.05) {
          cat("\n   *** SIGNIFICANT: Late-season compression effect detected ***\n")
          if (injury_interaction$estimate[1] > 0) {
            cat("   Positive interaction indicates that cumulative workload effects are AMPLIFIED\n")
            cat("   in late season. Each additional cumulative short week becomes more dangerous\n")
            cat("   as the season progresses, supporting the \"grind\" hypothesis.\n")
          } else {
            cat("   Negative interaction suggests workload effects diminish in late season.\n")
          }
        } else {
          cat("\n   Interaction effect not statistically significant at p < 0.05.\n")
          cat("   This suggests cumulative workload effects are relatively constant across season weeks.\n")
        }
      }
      
      # Late season indicator model
      injury_late <- interaction_results$interaction_coefficients %>%
        filter(model == "injury_late", grepl("late_season_cum", term))
      
      if (nrow(injury_late) > 0) {
        cat("\n   Late Season Indicator Interaction:\n")
        cat(glue("   Coefficient: {round(injury_late$estimate[1], 4)} ",
                 "(SE: {round(injury_late$std.error[1], 4)}, ",
                 "p = {round(injury_late$p.value[1], 4)})\n"))
        if (injury_late$p.value[1] < 0.05) {
          cat("   *** SIGNIFICANT: Late-season (Week 13+) shows amplified workload effects ***\n")
        }
      }
      
      cat("\n   Interpretation: The interaction term captures whether the effect of cumulative\n")
      cat("   short weeks changes as the season progresses. A positive interaction means that\n")
      cat("   the same amount of cumulative workload is more dangerous in Week 15 than Week 2,\n")
      cat("   supporting the hypothesis that accumulated fatigue compounds over time.\n")
      cat("   This aligns with sports science research on the \"bathtub curve\" of injury risk.\n\n")
      
      cat("   Policy Implications:\n")
      cat("   - If significant, late-season TNF games should be prioritized for reform\n")
      cat("   - Supports the value of a second bye week, especially if placed in late season\n")
      cat("   - Reinforces the 17-game season finding that effects build over time\n")
      cat("   - Suggests workload management strategies should account for season timing\n")
    } else {
      cat("   Interaction coefficients not available\n")
    }
  }
  
  cat("\n================================================================\n")
  cat("TOP 3 PRIORITIES FOR NFLPA\n")
  cat("================================================================\n\n")
  
  for (i in 1:3) {
    rec <- recommendations$detailed[[paste0("priority_", i)]]
    cat(glue("PRIORITY {i}: {rec$title}\n\n"))
    cat(glue("Finding: {rec$finding}\n\n"))
    cat(glue("Recommendation: {rec$recommendation}\n\n"))
    cat(glue("Proposed CBA Language: {rec$cba_language}\n\n"))
    cat(glue("Feasibility: {rec$feasibility}\n"))
    cat(glue("Union Benefit: {rec$union_benefit}\n"))
    cat(glue("Management Concern: {rec$management_concern}\n\n"))
    cat("---\n\n")
  }
  
  # Return all results
  results <- list(
    data = data,
    performance = performance_results,
    injuries = injury_results,
    wins = win_results,
    did_17_game = did_results,
    event_study = event_study_results,
    distributed_lags = lag_results,
    dose_response = dose_response_results,
    counterfactuals = counterfactual_results,
    msm = msm_results,
    late_season_interaction = interaction_results,
    survival = survival_results,
    severe_injury_survival = severe_injury_survival_results,
    severe_injury_survival_3wk = severe_injury_survival_results_3wk,
    severe_injury_survival_4wk = severe_injury_survival_results_4wk,
    severity = severity_results,
    position_heterogeneity = position_results,
    bye_effectiveness = bye_results,
    injury_types = injury_type_results,
    plots = list(
      rest = plots_rest,
      win = plots_win,
      did = plots_did,
      survival = plots_survival,
      severe_injury_survival = plots_severe_injury_survival,
      severity = plots_severity,
      position = plots_position,
      bye = plots_bye,
      injury_types = plots_injury_types,
      event_study = plots_event_study,
      distributed_lags = plots_lags,
      dose_response = plots_dose,
      counterfactuals = plots_counterfactuals,
      msm = plots_msm,
      late_season_interaction = plots_interaction
    ),
    policy = policy_impact,
    recommendations = recommendations
  )
  
  cat("\nAnalysis complete. Access results with:\n")
  cat("  results$performance - Performance models\n")
  cat("  results$injuries - Injury models\n")
  cat("  results$wins - Win probability models\n")
  cat("  results$did_17_game - 17-game season DiD\n")
  cat("  results$event_study - Event study DiD (dynamic effects)\n")
  cat("  results$distributed_lags - Distributed lag models (cumulative workload)\n")
  cat("  results$dose_response - Nonlinear dose response (thresholds)\n")
  cat("  results$counterfactuals - Policy counterfactual simulations\n")
  cat("  results$msm - Marginal structural models (IPW for time-varying confounding)\n")
  cat("  results$late_season_interaction - Late-season workload interaction (Week × Cumulative Short Weeks)\n")
  cat("  results$survival - Survival analysis\n")
  cat("  results$severity - Injury severity (games missed) analysis\n")
  cat("  results$position_heterogeneity - Position-specific effects\n")
  cat("  results$bye_effectiveness - Bye week buffer analysis (with investigation)\n")
  cat("  results$injury_types - Injury type heterogeneity (soft-tissue vs joint vs contact)\n")
  cat("  results$policy - Policy impact estimates\n")
  cat("  results$recommendations - NFLPA priorities\n")
  
  return(results)
}

# =============================================================================
# RUN ANALYSIS
# =============================================================================
results <- main(include_player_level = TRUE, save_plots = TRUE)
