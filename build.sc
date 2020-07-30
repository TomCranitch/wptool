import mill._
import mill.api.Loose
import mill.define.Target
import mill.scalalib._

object wptool extends ScalaModule {
    def scalaVersion = "2.13.3"
    override def mainClass = Some("wptool.WPTool")

    override def unmanagedClasspath = T {
        if (!ammonite.ops.exists(millSourcePath / "lib")) Agg()
        else Agg.from(ammonite.ops.ls(millSourcePath / "lib").map(PathRef(_)))
    }

    object test extends Tests {
        override def unmanagedClasspath: Target[Loose.Agg[PathRef]] = T {
            if (!ammonite.ops.exists(millSourcePath / "lib")) Agg()
            else Agg.from(ammonite.ops.ls(millSourcePath / "lib").map(PathRef(_)))
        }

        override def ivyDeps = Agg(
            ivy"org.scalactic::scalactic:3.2.0",
            ivy"org.scalatest::scalatest:3.2.0"
        )

        def testFrameworks = Seq("org.scalatest.tools.Framework")
    }
}
