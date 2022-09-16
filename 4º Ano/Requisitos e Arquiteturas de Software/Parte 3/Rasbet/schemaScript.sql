/* Logico: */

-- -----------------------------------------------------
-- Schema rasbet
-- -----------------------------------------------------

DROP SCHEMA IF EXISTS `abd`;

CREATE SCHEMA IF NOT EXISTS `abd` DEFAULT CHARACTER SET utf8mb4 COLLATE utf8mb4_0900_ai_ci ;
USE `a` ;

CREATE TABLE T (
    B int PRIMARY KEY NOT NULL,
    A int NOT NULL,
    C int NOT NULL
);
 
