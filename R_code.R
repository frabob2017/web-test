library(nlme)
library(splines)
library(lattice)
library(gridExtra)
library(modelr)
library(rsample)
library(rms)
library(groupdata2)
library(dplyr)  ##, lib="/content/drive/MyDrive/R_library")
library(tidyverse)
library(knitr) # kable()
library(lmerTest) #lmer()
library(Metrics)
library(lattice)
library(latticeExtra)

library(shiny)
library(rsconnect)
##library(shinytheme)

library(AzureAuth)
library(AzureStor)
library(AzureTableStor)
library(sendmailR)
library(shinythemes)
########################################
# Functions needed for the dynamic predictions #
########################################
# The following functions were taken from the JMbayes package.
# Small changes have been made.
IndvPred_lme <- function(lmeObject, newdata, timeVar, times = NULL, M = 200L,
                         interval = c("confidence", "prediction"),
                         all_times = FALSE,
                         level = 0.95, return_data = FALSE, seed = 1L) {
  if (!inherits(lmeObject, "lme") && !inherits(lmeObject, "lmeComponents"))
    stop("Use only with 'lme' or 'lmeComponents' objects.\n")
  interval <- match.arg(interval)
  if (inherits(lmeObject, "lme")) {
    data <- lmeObject$data
    
    ### the code “formYx <- formula(lmeObject)” assigns the formula of the fixed effects in a linear mixed-effects model to the variable formYx.
    formYx <- formula(lmeObject)
    mfX <- model.frame(terms(formYx), data = data)
    ### In R, a term is a symbolic description of the variables in a model formula. It is used to specify the relationship between the response variable and the predictor variables
    ### in a statistical model. The terms() function is used to extract the terms from a model formula 1. In the code you provided, attr(mfX, "terms") extracts the terms from the model
    ### formula stored in the mfX object. The resulting terms object is then assigned to the variable TermsX. This terms object can be used as an argument in other functions that require
    ### a terms object, such as lm() or lme()
    TermsX <- attr(mfX, "terms")
    
    ### the code “formYz <- formula(lmeObject$modelStruct$reStruct[1])” assigns the formula of the first random effect in a linear mixed-effects model to the variable formYz.
    formYz <- formula(lmeObject$modelStruct$reStruct[[1]])
    
    ### In R, the code “idVar <- names(lmeObject$modelStruct$reStruct)” assigns the names of the random effects in a linear mixed-effects model to the variable
    mfZ <- model.frame(terms(formYz), data = data)
    TermsZ <- attr(mfZ, "terms")
    idVar <- names(lmeObject$modelStruct$reStruct)
    
    ### In R, the code “betas <- fixef(lmeObject)” assigns the fixed effects coefficients of a linear mixed-effects model to the variable betas.
    ### On the other hand, the code “sigma <- lmeObject$sigma” assigns the residual standard deviation of the model to the variable sigma.
    betas <- fixef(lmeObject)
    sigma <- lmeObject$sigma
    ### The code D <- lapply(pdMatrix(lmeObject$modelStruct$reStruct), "*", sigma^2)[[1]] in R language is used to calculate the variance-covariance matrix of the random effects
    ### in a linear mixed-effects model
    D <- lapply(pdMatrix(lmeObject$modelStruct$reStruct), "*", sigma^2)[[1]]
    V <- vcov(lmeObject)
    
    times_orig <- data[[timeVar]]
    times_orig <- times_orig[!is.na(times_orig)]
  } else {
    formYx <- lmeObject$formYx
    TermsX <- lmeObject$TermsX
    formYz <- lmeObject$formYz
    TermsZ <- lmeObject$TermsZ
    idVar <- lmeObject$idVar
    betas <- lmeObject$betas
    sigma <- lmeObject$sigma
    D <- lmeObject$D
    V <- lmeObject$V
    times_orig <- lmeObject$times_orig
  }
  # drop missing values from newdata
  ### all_vars <- unique(c(all.vars(TermsX), all.vars(TermsZ))):
  ### This line of code creates a vector all_vars that contains all the unique variables in TermsX and TermsZ.
  ### Here, TermsX and TermsZ are objects that contain the terms of two different models.
  
  ###  all.vars() is an R function that extracts all the variable names from an expression. It returns a character vector of the names of all variables in the expression.
  ###  This line of code creates a new data frame newdata_nomiss by subsetting the original data frame newdata. The subset includes only those rows that have no missing values in any of the variables in all_vars.
  all_vars <- unique(c(all.vars(TermsX), all.vars(TermsZ)))
  ###  The complete.cases() function is used to identify rows with no missing values in the specified columns 1.
  ###  The resulting data frame newdata_nomiss will only contain rows with complete data for all variables in all_vars.
  newdata_nomiss <- newdata[complete.cases(newdata[all_vars]), ]
  
  
  # mfX_new <- model.frame(TermsX, data = newdata_nomiss): This line of code creates a model frame mfX_new using the terms in TermsX and the data in newdata_nomiss. A model frame is a data frame that contains the variables needed to use a formula and any additional arguments 1.
  # X_new <- model.matrix(formYx, mfX_new): This line of code creates a model matrix X_new using the formula formYx and the model frame mfX_new. A model matrix is a matrix that contains the predictor variables used in a linear regression model 2.
  # mfZ_new <- model.frame(TermsZ, data = newdata_nomiss): This line of code creates another model frame mfZ_new using the terms in TermsZ and the data in newdata_nomiss.
  # Z_new <- model.matrix(formYz, mfZ_new): This line of code creates another model matrix Z_new using the formula formYz and the model frame mfZ_new.
  # na_ind <- attr(mfX_new, "na.action"): This line of code extracts the indices of any missing values in the predictor variables from the model frame mfX_new.
  # y_new <- model.response(mfX_new, "numeric"): This line of code extracts the response variable from the model frame mfX_new.
  
  
  mfX_new <- model.frame(TermsX, data = newdata_nomiss)
  X_new <- model.matrix(formYx, mfX_new)
  mfZ_new <- model.frame(TermsZ, data = newdata_nomiss)
  Z_new <- model.matrix(formYz, mfZ_new)
  na_ind <- attr(mfX_new, "na.action")
  y_new <- model.response(mfX_new, "numeric")
  
  if (length(idVar) > 1)
    stop("the current version of the function only works with a single grouping variable.\n")
  if (is.null(newdata[[idVar]]))
    stop("subject id variable not in newdata.")
  
  id_nomiss <- match(newdata_nomiss[[idVar]], unique(newdata_nomiss[[idVar]]))
  n <- length(unique(id_nomiss))
  modes <- matrix(0.0, n, ncol(Z_new))
  post_vars <- DZtVinv <- vector("list", n)
  for (i in seq_len(n)) {
    id_i <- id_nomiss == i
    X_new_id <- X_new[id_i, , drop = FALSE]
    Z_new_id <- Z_new[id_i, , drop = FALSE]
    Vi_inv <- solve(Z_new_id %*% tcrossprod(D, Z_new_id) + sigma^2 * diag(sum(id_i)))
    DZtVinv[[i]] <- tcrossprod(D, Z_new_id) %*% Vi_inv
    modes[i, ] <- c(DZtVinv[[i]] %*% (y_new[id_i] - X_new_id %*% betas))
    t1 <- DZtVinv[[i]] %*% Z_new_id %*% D
    t2 <- DZtVinv[[i]] %*% X_new_id %*% V %*%
      crossprod(X_new_id, Vi_inv) %*% Z_new_id %*% D
    post_vars[[i]] <- D - t1 + t2
  }
  fitted_y <- c(X_new %*% betas) + rowSums(Z_new * modes[id_nomiss, , drop = FALSE])
  
  ###
  ###  This line control the time range to show
  ###
  if (is.null(times) || !is.numeric(times)) {
    ## Frank modify here
    ##times <- seq(min(times_orig), max(times_orig), length.out = 100)
    times <- seq(min(times_orig), 30.0, length.out = 300)
    ## times <- seq(min(newdata[[timeVar]]), max(newdata[[timeVar]]) + 10.0, length.out = 200)
  }
  id <- match(newdata[[idVar]], unique(newdata[[idVar]]))
  
  last_time <- tapply(newdata[[timeVar]], id, max)
  ## last_time <- tapply(newdata[[timeVar]], id, nth, n=-2)
  #last_time <- (last_time - 1.0)
  
  ##In this R code, lapply() is used to apply a function to each element of the last_time list. The function takes a single argument t, which represents each element of last_time.
  ## The function checks if the all_times variable is TRUE. If it is, the entire times vector is returned. If not, the function returns a subset of the times vector that includes only the elements greater than t.
  ## The resulting output is a list of vectors, where each vector contains the subset of times that are greater than the corresponding element of last_time.
  times_to_pred <- lapply(last_time, function (t)
    if (all_times) times else times[times > t])
  id_pred <- rep(seq_len(n), sapply(times_to_pred, length))
  #newdata_pred <- newdata_pred[id_pred, ]
  newdata_pred <- right_rows(newdata, newdata[[timeVar]], id, times_to_pred)
  newdata_pred[[timeVar]] <- unlist(times_to_pred)
  mfX_new_pred <- model.frame(TermsX, data = newdata_pred, na.action = NULL)
  X_new_pred <- model.matrix(formYx, mfX_new_pred)
  
  # '''
  # This R code calculates the inverse of a matrix Vi using the Woodbury matrix identity. The matrix Vi is defined as Z_new_id %*% tcrossprod(D, Z_new_id) + sigma^2 * diag(sum(id_i)),
  # where %*% denotes matrix multiplication, tcrossprod() computes the cross-product of two matrices, diag() creates a diagonal matrix, and sum() computes the sum of elements in a vector.
  # '''
  mfZ_new_pred <- model.frame(TermsZ, data = newdata_pred, na.action = NULL)
  Z_new_pred <- model.matrix(formYz, mfZ_new_pred)
  predicted_y <- c(X_new_pred %*% betas) +
    rowSums(Z_new_pred * modes[id_pred, , drop = FALSE])
  set.seed(seed)
  ##  The code betas_M <- MASS::mvrnorm(M, betas, V) in R generates a random sample of size M from a multivariate normal distribution with mean vector betas
  ##  and covariance matrix V
  betas_M <- MASS::mvrnorm(M, betas, V)
  modes_fun <- function (betas) {
    t(mapply("%*%", DZtVinv, split(y_new - X_new %*% betas, id_nomiss)))
  }
  
  ##
  ##  mapply() and lapply() are both functions in R used to apply a function to a list or vector. However, they differ in their input and output formats.
  ## lapply() takes a list or vector as input and returns a list of the same length as the input, where each element of the output list is the result of applying the function
  ## to the corresponding element of the input list 12.
  ## On the other hand, mapply() takes multiple lists or vectors as input and applies the function to corresponding elements of each list or vector.
  ## It returns a vector or array of results, depending on the output format of the function 13.
  ## In summary, lapply() is used to apply a function to each element of a list or vector and returns a list, while mapply() is used to apply a function
  ## to corresponding elements of multiple lists or vectors and returns a vector or array.
  ##
  
  modes_M <- lapply(split(betas_M, row(betas_M)), modes_fun)
  matrix_row <- function (m, i) m[i, , drop = FALSE]
  modes_M <- lapply(seq_len(n), function (i) t(sapply(modes_M, matrix_row, i = i)))
  b_M <- modes_M
  for (i in seq_len(n)) {
    b_M[[i]] <- t(apply(modes_M[[i]], 1, MASS::mvrnorm, n = 1, Sigma = post_vars[[i]]))
  }
  n_pred <- length(predicted_y)
  sampled_y <- matrix(0.0, n_pred, M)
  for (m in seq_len(M)) {
    betas_m <- betas_M[m, ]
    b_m <- t(sapply(b_M, function (x) x[m, ]))
    mean_m <- c(X_new_pred %*% betas_m) +
      rowSums(Z_new_pred * b_m[id_pred, , drop = FALSE])
    sampled_y[, m] <- if (interval == "confidence") mean_m
    else rnorm(n_pred, mean_m, lmeObject$sigma)
  }
  low <- apply(sampled_y, 1, quantile, probs = (1 - level) / 2)
  upp <- apply(sampled_y, 1, quantile, probs = 1 - (1 - level) / 2)
  rm(list = ".Random.seed", envir = globalenv())
  if (!return_data) {
    list(times_to_pred = times_to_pred, predicted_y = predicted_y,
         low = low, upp = upp)
  } else {
    out_data <- rbind(newdata, newdata_pred)
    out_data$pred <- c(fitted_y, predicted_y)
    out_data$low <- c(rep(NA, length(fitted_y)), low)
    out_data$upp <- c(rep(NA, length(fitted_y)), upp)
    out_data[order(out_data[[idVar]], out_data[[timeVar]]), ]
  }
}

right_rows <- function(data, times, ids, Q_points) {
  ## The second line creates a factor variable fids from the ids argument, which is used to split the data frame by unique values of ids.
  fids <- factor(ids, levels = unique(ids))
  if (!is.list(Q_points))
    Q_points <- split(Q_points, row(Q_points))
  ind <- mapply(findInterval, Q_points, split(times, fids))
  ind[ind < 1] <- 1
  rownams_id <- split(row.names(data), fids)
  ind <- mapply(`[`, rownams_id, split(ind, col(ind)))
  data[c(ind), ]
}


DynPlots <- function(model.output = model.output, newdata, timeVar,
                     main_title = "Dynamic predictions"){
  
  
  # Load individual prediction ------------------------------------
  data <- model.output$data
  formYx <- formula(model.output)
  yOutcome <- formYx[[2]]
  IndvPrediction95 <- IndvPred_lme(lmeObject = model.output, newdata, timeVar,
                                   times = NULL, M = 500, interval = "prediction", return_data = TRUE)
  IndvPrediction68 <- IndvPred_lme(lmeObject = model.output, newdata, timeVar,
                                   times = NULL, M = 500, interval = "prediction", return_data = TRUE, level = 0.68)
  pred95 <- IndvPrediction95[which(!is.na(IndvPrediction95$low)),]
  pred68 <- IndvPrediction68[which(!is.na(IndvPrediction68$low)),]
  nopred <- IndvPrediction95[which(is.na(IndvPrediction95$low)),]
  timeVariable <- pred95[[timeVar]]
  
  # Generating plot ---------------------------------------------------i--
  # p95_1 = as.numeric( unlist(c(pred95[,"Echo_Age_Years"], rev(pred95[,"Echo_Age_Years"]))) )
  # p95_2 = as.numeric( unlist( c(pred95[,"upp"], rev(pred95[,"low"])) ) )
  
  # p68_1 = as.numeric( unlist(c(pred68[,"Echo_Age_Years"], rev(pred68[,"Echo_Age_Years"]))) )
  # p68_2 = as.numeric( unlist( c(pred68[,"upp"], rev(pred95[,"low"])) ) )
  
  p95_1 = as.numeric( unlist(c(pred95[,"Echo_Age_Years"], (pred95[,"Echo_Age_Years"]))) )
  p95_2 = as.numeric( unlist( c(pred95[,"upp"], (pred95[,"low"])) ) )
  
  p68_1 = as.numeric( unlist(c(pred68[,"Echo_Age_Years"], (pred68[,"Echo_Age_Years"]))) )
  p68_2 = as.numeric( unlist( c(pred68[,"upp"], (pred95[,"low"])) ) )
  
  ##jpeg("img_folder/jpg_img.jpg")
  ### Generating plot -----------------------------------------------------
  jpg_img <- xyplot(pred ~ timeVariable , main = main_title, data = pred95,
         type = "l", col = rgb(0.6769,0.4447,0.7114, alpha = 1), lty = c(1, 2, 2), lwd = 3,
         ylim = c(0,6), xlim = c(0,20), ylab = list(yOutcome, cex = 1.5), xlab = list(timeVar, cex
                                                                                      = 1.5),
         scales = list(x = list(cex = 1.3) , y = list(cex = 1.3)),
         panel = function(x, y, ...) {
           panel.xyplot(x, y, ...)
           panel.polygon(c(pred95[,"Echo_Age_Years"], rev(pred95[,"Echo_Age_Years"])),
                         c(pred95[,"upp"], rev(pred95[,"low"])),
                         border = NA,
                         col = rgb(0.6769,0.4447,0.7114, alpha = 0.2))
           panel.polygon(c(pred68[,"Echo_Age_Years"], rev(pred68[,"Echo_Age_Years"])),
                         c(pred68[,"upp"], rev(pred68[,"low"])),
                         border = NA,
                         col =rgb(0.6769,0.4447,0.7114, alpha = 0.4))
           panel.points(x = nopred[[timeVar]], y = nopred[[yOutcome]], cex = 1.2, pch = 16, col =
                          "black");
           panel.lines(x = rep(tail(nopred[[timeVar]], n = 1), 20), y = seq(0, 6, length =
                                                                              20), col = "grey", lty = 3, lwd = 2)
         })
  # print(jpg_img)
  # dev.off()
  return(jpg_img)
}

process_data_plot <- function(dat, predict_age) {
  dat_abstract <- dat
  #print(colnames(dat_abstract))
  #colnames(dat_abstract)[colnames(dat_abstract)=='Age at Echo'] <- 'Echo_Age_Years'
  colnames(dat_abstract)[colnames(dat_abstract)=='Sex'] <- 'female'
  colnames(dat_abstract)[colnames(dat_abstract)=='Aortic_Root_Dimension'] <- 'aort_root_new'
  colnames(dat_abstract)[colnames(dat_abstract)=='Weight (kg)'] <- 'Weight'
  colnames(dat_abstract)[colnames(dat_abstract)=='Height (cm)'] <- 'Height'
  colnames(dat_abstract)[colnames(dat_abstract)=='Aortic.root.z.score'] <- 'z_aort_root'
  #print(colnames(dat_abstract))

  dat_abstract$female = dat_abstract$female - 1
  nd <- dat_abstract
  nd <-nd[with(nd,order(Echo_Age_Years)),]

  # ## step 2: to get the PREDIICTION interval
  pred_dat_001_95 <- IndvPred_lme(model_ARS_Dem,newdata = nd, timeVar = "Echo_Age_Years", M = 500, return_data = F)
  pred_dat_001_68 <- IndvPred_lme(model_ARS_Dem,newdata = nd, timeVar = "Echo_Age_Years", M = 500, return_data = F,level = 0.68)
  pred_times=pred_dat_001_95$times_to_pred$'1'
  ##print(pred_times)
  pred=pred_dat_001_95$predicted_y

  lower95=pred_dat_001_95$low
  upper95=pred_dat_001_95$upp
  lower68=pred_dat_001_68$low
  upper68=pred_dat_001_68$upp

  dat <- data.frame(pred_times)
  dat$pred = pred
  dat$lower95=lower95
  dat$upper95=upper95
  dat$lower68=lower68
  dat$upper68=upper68
  #
  #
  predicted_value<- approx(dat$pred_times, dat$pred, xout=predict_age)$y

 
  jpg_img <- DynPlots(model.output = model_ARS_Dem, newdata = nd,
               timeVar = "Echo_Age_Years",
               main_title = "predicted aortic size at age ")
  
 

  return(jpg_img)


}

process_data_func2 <- function(dat, predict_age) {
  dat_abstract <- dat
  #print(colnames(dat_abstract))
  #colnames(dat_abstract)[colnames(dat_abstract)=='Age at Echo'] <- 'Echo_Age_Years'
  colnames(dat_abstract)[colnames(dat_abstract)=='Sex'] <- 'female'
  colnames(dat_abstract)[colnames(dat_abstract)=='Aortic_Root_Dimension'] <- 'aort_root_new'
  colnames(dat_abstract)[colnames(dat_abstract)=='Weight (kg)'] <- 'Weight'
  colnames(dat_abstract)[colnames(dat_abstract)=='Height (cm)'] <- 'Height'
  colnames(dat_abstract)[colnames(dat_abstract)=='Aortic.root.z.score'] <- 'z_aort_root'
  #print(colnames(dat_abstract))
  
  dat_abstract$female = dat_abstract$female - 1
  nd <- dat_abstract
  nd <-nd[with(nd,order(Echo_Age_Years)),]
  
  # ## step 2: to get the PREDIICTION interval
  pred_dat_001_95 <- IndvPred_lme(model_ARS_Dem,newdata = nd, timeVar = "Echo_Age_Years", M = 500, return_data = F)
  pred_dat_001_68 <- IndvPred_lme(model_ARS_Dem,newdata = nd, timeVar = "Echo_Age_Years", M = 500, return_data = F,level = 0.68)
  pred_times=pred_dat_001_95$times_to_pred$'1'
  ##print(pred_times)
  pred=pred_dat_001_95$predicted_y
  
  lower95=pred_dat_001_95$low
  upper95=pred_dat_001_95$upp
  lower68=pred_dat_001_68$low
  upper68=pred_dat_001_68$upp
  
  dat <- data.frame(pred_times)
  dat$pred = pred
  dat$lower95=lower95
  dat$upper95=upper95
  dat$lower68=lower68
  dat$upper68=upper68
  #
  #
  predicted_value<- c(approx(dat$pred_times, dat$pred, xout=predict_age)$y, approx(dat$pred_times, dat$lower95, xout=predict_age)$y, approx(dat$pred_times, dat$upper95, xout=predict_age)$y )
  predicted_value <- round(predicted_value, 3)
  
  # DynPlots(model.output = model_ARS_Dem, newdata = nd,
  #          timeVar = "Echo_Age_Years",
  #          main_title = "predicted aortic size at age ")
  
  return( predicted_value)
  
}



# ##dat_tch_final <- readRDS("./dat_tch_final.05.10.2023.rds")
# 
# dat_tch_final <- readRDS("//tccdav1b/Cardio_S/Morris/CLARITY/Frank/Aortic_Size_Prediction/CLARITY/rds/dat_tch_final.05.10.2023.rds")
# #evaluate not including the 16 yr as knot location to avoid predictions descending, use # prior to comma
# model_ARS_Dem <- lme(aort_root_new ~ female * ns(Echo_Age_Years, knots = c(2, 6, 10, 16
# )),
# data = dat_tch_final,
# random = list(ID =
#                 pdDiag(form = ~ ns(Echo_Age_Years, knots = c(2, 6, 10, 16
#                 )))),
# na.action = na.exclude,
# control = lmeControl(maxIter = 1e8, msMaxIter = 1e8))
# 
# saveRDS(model_ARS_Dem, '//tccdav1b/Cardio_S/Morris/CLARITY/Frank/Aortic_Size_Prediction/CLARITY/rds/tch_data_trained_model.rds')



## model_ARS_Dem <- readRDS("//tccdav1b/Cardio_S/Morris/CLARITY/Frank/Aortic_Size_Prediction/CLARITY/rds/tch_data_trained_model.rds")
## model_ARS_Dem <- readRDS("C:\\Users\\yxcai\\Documents\\R_code\\web-test\\tch_data_trained_model.rds")
model_ARS_Dem <- readRDS("./tch_data_trained_model.rds")

names(tags)

ui <- fluidPage(tags$style("body { background-color: #ADD8E6; }"),
  titlePanel(tags$h1(tags$b("Predict future Aortic Size based on the previous information for Marfan Syndrome patients"), align = "center") ),
  tags$br(),
  tags$br(),
  sidebarLayout( 
    sidebarPanel( width = 5,
      HTML("<h3>Step 1: Download the template file to fill the information</h3>"),
      ##tags$a("you can follow the video lecture", href = "https://www.youtube.com/watch?v=s4YKMFFiySI"),
      downloadButton("download_data", "Step1: please Download the template file", width = 2),
      tags$br(),
      HTML("<h3>Step 2: upload your previous aortic size related information defined in CSV file</h4>"),
      fileInput("file", " "),
      numericInput("age_need_prediction", label = "the age of aortic size need to predict:", value= 15.0),
      actionButton("submit", "Submit"),
      tags$br(),
      HTML("<h3>Step 3: optional step,enter your email to receive the results and the data will be saved and used for improving the AI model</h3>"),
      textInput("email"," "),
      HTML("<h4> after you enter your email, click save button  </h4>"),
      actionButton("save_file", "Save the data"),
      # HTML("<h4> ************************</h4>"),
    ),
    
    
    mainPanel( width = 7,
      tableOutput("data"),
      plotOutput(outputId = "my_plot"),
      # tags$br(),
      # tags$br(),
      tags$h3(textOutput("result"))
    )
  ),
  widths = c(1, 1)
 
)

server <- function(input, output) {

  data <- reactive({
    file <- input$file
    if (is.null(file)) {
      return(NULL)
    }
    read.csv(file$datapath)
  })

  output$data <- renderTable({
    data()
  })
  
  # Download the data when the download button is clicked
  output$download_data <- downloadHandler(
    filename = function() {
      "template.csv"
    },
    content = function(file) {
      file.copy("template.csv", file)
    }
  )

  output_string <- reactive({  
  result<-process_data_func2(data(), input$age_need_prediction)
  paste("The predicted aortic size of at the age ", input$age_need_prediction, " is ", result[[1]], " cm; \n",'The predicted lower limit is ', result[[2]], "cm; \n",'The predicted upper limit is ', result[[3]], "cm; ")
  })
  
  observeEvent(input$submit, { output$result <- renderText({ output_string()  } ) }  )
  
  ##  Keep this code
  # observeEvent(input$submit, { output$result <- renderText({ result<-process_data_func2(data(), input$age_need_prediction)
  # paste("The predicted aortic size of at the age ", input$age_need_prediction, " is ", result[[1]], " cm; \n",'The predicted lower limit is ', result[[2]], "cm; \n",'The predicted upper limit is ', result[[3]], "cm; ")
  #                            } ) }  )
  
  # observeEvent(input$submit, {  my_plot <- process_data_plot(data(), input$age_need_prediction) 
  #                               output$my_plot <- renderPlot( { process_data_plot(data(), input$age_need_prediction ) } )
  #                           ggsave("img_folder/jpg_img", device = 'jpeg')   }  )
  
  frank_plot <-  reactive({  process_data_plot(data(), input$age_need_prediction) })
  
  observeEvent(input$submit, {  
                                output$my_plot <- renderPlot( { frank_plot()  } )
                                ##frank_plot <- ggplotify(frank_plot)
                                ##trellis.device("img_folder/jpg_img", type = "jpeg")
                                  }   )

  # 
  # observeEvent(input$save_file, { ## for Table
  #   my_table_endpoint <- table_endpoint(
  #     "https://rdeploymenta2e3.table.core.windows.net",   ## storage endpoint
  #     sas = "?sv=2022-11-02&ss=t&srt=sco&sp=rwdlacu&se=2025-01-01T01:21:30Z&st=2023-12-27T17:21:30Z&spr=https&sig=yYkHHuxJ2MVEadbeJkUSq9zmpN405Ngui9ShrNR9B%2FA%3D")
  #   my_table <- storage_table(my_table_endpoint, "clarity4input4database")
  #   AzureTableStor::import_table_entities(my_table, data(), row_key=row.names(data()), partition_key=input$email )      ## as.character(data()$ID
  #   
  #    }  )
  

  # observeEvent(input$save_file, {
  #               file_name <- gsub("@", "_", input$email )
  #               file_name <- paste0("img_folder/", file_name, '.jpg')
  #               jpeg(file_name)
  #               print(frank_plot())
  #               dev.off()
  #               
  #               attachment <- mime_part(x = file_name )
  #               body <- output_string()
  # 
  #               sendmailR::sendmail( from = "yu.cai.tch@gmail.com",
  #                                    to =  c(input$email),
  #                                    subject = "Confirmation of Receive Your Data",
  #                                    ##msg = mime_part("Confirmation of Receive Your Data"),
  #                                    msg = list(body, attachment),
  #                                    engine = "curl",
  #                                    engineopts = list(username = "yu.cai.tch@gmail.com", password = "ybbm kusp woaq srbn"),
  #                                    control=list(smtpServer="smtp://smtp.gmail.com:587", verbose = TRUE) )
  #               } )

}

shinyApp(ui = ui, server = server)



##print( output$data)
##
## This code I need to study
##

# ui <- fluidPage(
#   sidebarLayout(
#     sidebarPanel(
#       actionButton("repeat1", "Repeat 1")
#     ),
#     mainPanel(
#       uiOutput("dynamic_sidebar")
#     )
#   )
# )
# 
# server <- function(input, output, session) {
#   observeEvent(input$repeat1, {
#     # Increment the counter for dynamic sidebar generation
#     counter <- input$repeat1
#     # Create a unique ID for the dynamic sidebar
#     dynamic_sidebar_id <- paste0("dynamic_sidebar_", counter)
# 
#     # Dynamically generate a new sidebarPanel
#     output$dynamic_sidebar <- renderUI({
#       tagList(
#         # Previous dynamic sidebars
#         lapply(1:counter, function(i) {
#           conditionalPanel(
#             condition = sprintf('input.%s > 0', paste0("repeat", i)),
#             sidebarPanel(
#               h3(paste("Dynamic Sidebar", i)),
# 
#               # Add your dynamic sidebar content here
#             )
#           )
#         }),
#         # New dynamic sidebar
#         conditionalPanel(
#           condition = sprintf('input.%s > 0', paste0("repeat", counter)),
#           sidebarPanel(
#             h3(paste("Dynamic Sidebar", counter)),
#             actionButton("repeat2", "Repeat 2")
#             # Add your dynamic sidebar content here
#           )
#         )
#       )
#     })
#   })
# }
# 
# shinyApp(ui, server)
#  






# # Define UI
# ui <- fluidPage(##theme = shinytheme("cerulean"),
#                 sidebarPanel(
#                   HTML("<h3>Input parameters</h3>"),
#                   #tags$h3("Input:"),
#                   numericInput("age", label = "the age of the echo:", value= 2.0),
#                   numericInput("aortic_size", label = "the size of arotic at the first echo (cm):", value= 2.3),
#                   actionButton("submitbutton", "Submit", class = "btn btn-primary"),
#                   actionButton("more_data", "more data", class = "btn btn-primary")
#                 ), # sidebarPanel
# 
#                 # sidebarPanel(
#                 #   HTML("<h3>Input parameters</h3>"),
#                 #   #tags$h3("Input:"),
#                 #   numericInput("age", label = "the age of the echo:", value= 2.0),
#                 #   numericInput("aortic_size", label = "the size of arotic at the first echo (cm):", value= 2.3),
#                 #   actionButton("more_data", "more data", class = "btn btn-primary"),
#                 # ), # sidebarPanel
#                 # sidebarPanel(
#                 #   HTML("<h3>Input parameters</h3>"),
#                 #   #tags$h3("Input:"),
#                 #   numericInput("age", label = "the age of the echo:", value= 2.0),
#                 #   numericInput("aortic_size", label = "the size of arotic at the first echo (cm):", value= 2.3),
#                 #   actionButton("more_data", "more data", class = "btn btn-primary"),
#                 # ), # sidebarPanel
#                 # sidebarPanel(
#                 #   HTML("<h3>Input parameters</h3>"),
#                 #   #tags$h3("Input:"),
#                 #   numericInput("age", label = "the age of the echo:", value= 2.0),
#                 #   numericInput("aortic_size", label = "the size of arotic at the first echo (cm):", value= 2.3),
#                 #   actionButton("more_data", "more data", class = "btn btn-primary"),
#                 # ), # sidebarPanel
#                 # sidebarPanel(
#                 #   HTML("<h3>Input parameters</h3>"),
#                 #   #tags$h3("Input:"),
#                 #   numericInput("age", label = "the age of the echo:", value= 2.0),
#                 #   numericInput("aortic_size", label = "the size of arotic at the first echo (cm):", value= 2.3),
#                 #   actionButton("more_data", "more data", class = "btn btn-primary"),
#                 # ), # sidebarPanel
#                 # sidebarPanel(
#                 #   HTML("<h3>Input parameters</h3>"),
#                 #   #tags$h3("Input:"),
#                 #   numericInput("age", label = "the age of the echo:", value= 2.0),
#                 #   numericInput("aortic_size", label = "the size of arotic at the first echo (cm):", value= 2.3),
#                 #   actionButton("more_data", "more data", class = "btn btn-primary"),
#                 # ), # sidebarPanel
# 
#                 mainPanel(
#                   h1("predicted value"),
#                   verbatimTextOutput("txtout"),
#                 ) # mainPanel
# 
# ) # fluidPage
# #
# #
# # # Define server function
# server <- function(input, output) {
# 
#   output$txtout <- renderText({
#     paste( input$age, input$aortic_size, sep = " " )
#   })
# } # server
# #
# #
# # # Create Shiny object
# shinyApp(ui = ui, server = server)
# # 
