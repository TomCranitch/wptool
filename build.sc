import coursier.ivy.IvyRepository
import mill._
import mill.api.Loose
import mill.define.Target
import mill.scalalib._
import scalafmt._
import coursier.maven.MavenRepository

object wptool extends ScalaModule with ScalafmtModule {
    def scalaVersion = "2.13.3"
    override def mainClass = Some("wptool.WPTool")

    override def unmanagedClasspath = T {
        if (!ammonite.ops.exists(millSourcePath / "lib")) Agg()
        else Agg.from(ammonite.ops.ls(millSourcePath / "lib").map(PathRef(_)))
    }

	override def repositories = super.repositories ++ Seq(
  		MavenRepository("http://logicrunch.research.it.uu.se/maven/")
	)

	
    override def ivyDeps = Agg(
        ivy"org.sosy-lab:java-smt:3.7.0",
		ivy"org.scala-lang:scala-reflect:2.13.3",
    )


    object test extends Tests {
        override def unmanagedClasspath: Target[Loose.Agg[PathRef]] = T {
            if (!os.exists(millSourcePath / os.up / "lib")) Agg()
            else Agg.from(os.list(millSourcePath / os.up / "lib").map(PathRef(_)))
        }

        override def ivyDeps = Agg(
            ivy"org.scalactic::scalactic:3.2.0",
            ivy"org.scalatest::scalatest:3.2.0"
        )

        def testFrameworks = Seq("org.scalatest.tools.Framework")
    }
}
