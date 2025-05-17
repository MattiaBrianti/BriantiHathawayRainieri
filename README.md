# Student&Companies (S&C) 🎓🏢

This project was developed as part of the **Software Engineering 2** course, where we were asked to produce both the Requirement Analysis and Specification Document (RASD) 📄 and the Design Document (DD) 📐 for the application.

**Student&Companies** is a platform to match university students looking for internships with companies offering them. It supports:

- 📝 Profiling students by experience, skills and attitudes (CVs).  
- 📢 Advertising internships by companies (domain, tasks, technologies, terms).  
- 🤖 Recommendation mechanisms (keywords, statistical analyses).  
- 🕵️‍♂️ Selection workflows (contacts, interviews, structured questionnaires).  
- 📊 Feedback collection and suggestions to improve CVs and project descriptions.  
- 🛠️ Monitoring of ongoing internships and complaint management by universities.

## 🤝 Authors
- **[Mattia Brianti](https://github.com/MattiaBrianti)**
- **[Alex Hathaway](https://github.com/Alexhath)**
- **[Mattia Rainieri](https://github.com/mattiarainieri)**

## 📂 Repository Structure

- `/RASD` – RASD document (LaTeX source & assets)  
- `/dd` – DD document (LaTeX source, diagrams, test plan)  
- `/DeliveryFolder` – Compiled PDFs (`RASDv1.1.pdf`, `RASDv1.pdf`, `DDv1.pdf`)  
- `/Presentation` – Final presentation PDF  

## 🔧 Build & View Documents

1. Install a TeX distribution (e.g., TeX Live, MiKTeX).  
2. Compile RASD:
   ```sh
   cd RASD
   pdflatex main.tex
   bibtex bibliography
   pdflatex main.tex && pdflatex main.tex
   ```
3. Compile DD:
   ```sh
   cd dd
   ./pdflatex-with-vars.sh dd.tex
   ```
4. Find generated PDFs in the same folder or in `/DeliveryFolder`.

## 📬 Contact

For questions or improvements, please open an issue or submit a pull request.
