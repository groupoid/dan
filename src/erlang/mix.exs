defmodule Dan.MixProject do
  use Mix.Project

  def project do
    [
      app: :dan,
      version: "0.3.10",
      description: "The Dan Programming Language",
      deps: deps(),
      package: package()
    ]
  end

  def application do
    [ extra_applications: [ :logger ] ]
  end

  def deps do
    [
      {:ex_doc, ">= 0.0.0", only: :dev}
    ]
  end

  def package() do
    [
      files: [ "README.md", "LICENSE" ],
      licenses: ["ISC"],
      maintainers: ["Namdak Tonpa"],
      name: :dan,
      links: %{"GitHub" => "https://github.com/groupoid/dan"}
    ]
  end

end
