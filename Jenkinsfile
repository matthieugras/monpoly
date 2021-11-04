pipeline {
  agent {
    dockerfile {
      filename 'Dockerfile'
      dir 'ci'
      additionalBuildArgs "--build-arg jenkins_id=\$(id -u jenkins)"
    }
  }
  stages {
    stage('Build') {
      steps {
        sh 'ci/compile.sh'
      }
    }
  }
  post {
    success {
      archiveArtifacts artifacts: 'binaries/*', fingerprint: true
    }
  }
}
