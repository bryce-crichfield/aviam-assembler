ThisBuild / version := "0.1.0-SNAPSHOT"

ThisBuild / scalaVersion := "3.1.2"

lazy val root = (project in file("."))
  .settings(
    name := "aviam_asm"
  )

// https://mvnrepository.com/artifact/org.typelevel/cats-core
libraryDependencies ++= Seq(
  "org.typelevel" %% "cats-core" % "2.7.0",
  "org.typelevel" %% "shapeless3-deriving" % "3.0.1"
)
